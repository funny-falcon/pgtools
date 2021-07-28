#include "postgres.h"

#include "access/htup_details.h"
#include "utils/builtins.h"
#include "utils/memutils.h"
#include "lib/stringinfo.h"
#include "port/pg_bitutils.h"
#include "nodes/bitmapset.h"

#include "integerset2.h"

#define ONE ((bitmapword)1)
#if BITS_PER_BITMAPWORD == 64
#define SHIFT 6
#define pg_popcountW pg_popcount64
#else
#define SHIFT 5
#define pg_popcountW pg_popcount32
#endif
#define START(x) ((x) >> SHIFT)
#define STARTN(x, n) ((x) >> (SHIFT*(n)))
#define NBIT(x) ((x) & (((uint64)1 << SHIFT)-1))
#define BIT(x) (ONE << NBIT(x))
#define NBITN(x, n) NBIT(STARTN(x, (n)-1))
#define BITN(x, n) (ONE << NBITN((x), (n)))

/*
 * Compressed leaf bitmap is indexed with 2 level bitmap index with
 * 1 byte in root level. Therefore there is 8 bytes in second level
 * and 64 bytes in third level.
 */
#define LEAF_SHIFT (3+3+3)
#define LEAF_BITS (1 << LEAF_SHIFT)
#define LEAF_BYTES (LEAF_BITS / 8)
#define LBYTE(x) (((x) / 8) & (LEAF_BYTES-1))
#define LBIT(x) (1 << ((x) & 7));

#define CHUNK_LEAFS BITS_PER_BITMAPWORD
#define CHUNK_SHIFT (LEAF_SHIFT + SHIFT)
#define CSTART(x) ((x) & ~(((uint64)1 << CHUNK_SHIFT)-1))
#define CPOS(x) NBIT((x) >> LEAF_SHIFT)

#define VAL_TO_PAGE(val) ((val) >> LEAF_SHIFT)
#define VAL_TO_CHUNK(val) ((val) >> CHUNK_SHIFT)
#define TRIE_LEVELS (64 / SHIFT)

#define ISAllocBatch (1<<18)

typedef struct IntsetAllocator IntsetAllocator;
struct IntsetAllocator
{
	Size	total_size;
	Size	alloc_size;
	Size	pos;
	Size	limit;
	uint8  *current;
	List   *chunks;
};

/* TRIE (HAMT like) */
typedef struct IntsetTrieVal IntsetTrieVal;
typedef struct IntsetTrieElem IntsetTrieElem;
typedef void* (*trie_alloc)(Size size, void *arg);
typedef struct IntsetTrie IntsetTrie;

struct IntsetTrieElem
{
	uint64	key;
	bitmapword	bitmap;
	union
	{
		void		*val;
		IntsetTrieElem	*children;
	}			p;
};

struct IntsetTrie
{
	trie_alloc	alloc;
	void *alloc_arg;

	int root_level;
	IntsetTrieElem	root;
	uint32 n[TRIE_LEVELS - 1];
	IntsetTrieElem l[TRIE_LEVELS - 1][BITS_PER_BITMAPWORD];
};

struct IntsetTrieVal
{
	bitmapword	bitmap;
	void	   *val;
};

/* Intset */

typedef enum IntsetLeafType IntsetLeafType;
typedef struct IntsetLeafBitmap IntsetLeafBitmap;
typedef struct IntsetLeafEmbed IntsetLeafEmbed;
typedef union IntsetLeafHeader IntsetLeafHeader;
/* alias for pointer */
typedef IntsetLeafHeader IntsetChunk;
typedef struct IntsetLeafBuilder IntsetLeafBuilder;
typedef struct IntsetChunkBuilder IntsetChunkBuilder;

#define bm2(b,c) (((b)<<1)|(c))
enum IntsetLeafType {
	LT_RAW     = bm2(0, 0),
	LT_INVERSE = bm2(0, 1),
	LT_SPARSE  = bm2(1, 0),
	LT_EMBED   = bm2(1, 1),
};

struct IntsetLeafBitmap
{
	IntsetLeafType	type:2;
	uint32  minbyte:6;
	uint32  maxbyte:6;
	uint32	offset:16;
};

struct IntsetLeafEmbed
{
	IntsetLeafType	type:2;
	uint32	v0:9;
	uint32	v1:9;
	uint32	v2:9;
};

union IntsetLeafHeader
{
	IntsetLeafBitmap	b;
	IntsetLeafEmbed		e;
	uint32	v;
};

StaticAssertDecl(sizeof(IntsetLeafBitmap) == sizeof(IntsetLeafEmbed),
		"incompatible bit field packing");
StaticAssertDecl(sizeof(IntsetLeafBitmap) == sizeof(uint32),
		"incompatible bit field packing");


struct IntsetLeafBuilder
{
	uint16	nvals;
	uint16	embed[3];
	uint8	minbyte;
	uint8	maxbyte;
	uint8	bytes[LEAF_BYTES];
};

struct IntsetChunkBuilder
{
	uint64	chunk;
	bitmapword bitmap;
	IntsetLeafBuilder leafs[CHUNK_LEAFS];
};

struct IntegerSet2
{
	uint64	firstvalue;
	uint64	nvalues;

	IntsetAllocator alloc;

	IntsetChunkBuilder current;
	IntsetTrie trie;
};


/* Allocator functions */

static void *intset2_alloc(Size size, IntsetAllocator *alloc);
static void  intset2_alloc_free(IntsetAllocator *alloc);

/* Trie functions */

static inline void intset2_trie_init(IntsetTrie *trie,
									 trie_alloc alloc,
									 void* arg);
static void intset2_trie_insert(IntsetTrie *trie,
								uint64 key,
								IntsetTrieVal val);
static IntsetTrieVal intset2_trie_lookup(IntsetTrie *trie, uint64 key);

/* Intset functions */

static uint8 intset2_leafbuilder_add(IntsetLeafBuilder *leaf, uint64 v);
static inline bool intset2_leafbuilder_is_member(IntsetLeafBuilder *leaf,
												 uint64 v);
static uint8 intset2_chunkbuilder_add(IntsetChunkBuilder *chunk, uint64 v);
static bool intset2_chunkbuilder_is_member(IntsetChunkBuilder *chunk,
										   uint64 v);
static bool intset2_chunk_is_member(IntsetChunk *chunk,
									bitmapword bitmap,
									uint64 v);

static void intset2_compress_current(IntegerSet2 *intset);

static inline uint8 pg_popcount8(uint8 b);
static inline uint8 pg_popcount8_lowbits(uint8 b, uint8 nbits);
static inline uint8 pg_popcount_small(uint8 *b, uint8 len);
static inline uint32 intset2_compact(uint8 *dest, uint8 *src, uint8 len, bool inverse);

/* Allocator */

static void*
intset2_alloc(Size size, IntsetAllocator *alloc)
{
	Assert(size < ISAllocBatch);

	size = MAXALIGN(size);

	if (alloc->limit - alloc->pos < size)
	{
		alloc->current = palloc0(ISAllocBatch);
		alloc->chunks = lappend(alloc->chunks, alloc->current);
		alloc->pos = 0;
		alloc->limit = ISAllocBatch;
		alloc->total_size += ISAllocBatch;
	}

	alloc->pos += size;
	alloc->alloc_size += size;
	return alloc->current + (alloc->pos - size);
}

static void
intset2_alloc_free(IntsetAllocator *alloc)
{
	list_free_deep(alloc->chunks);
}

/* Trie */

static inline void
intset2_trie_init(IntsetTrie *trie, trie_alloc alloc, void* arg)
{
	memset(trie, 0, sizeof(*trie));
	trie->root_level = -1;
	trie->alloc = alloc;
	trie->alloc_arg = arg;
}

static void
intset2_trie_insert(IntsetTrie *trie, uint64 key, IntsetTrieVal val)
{
	IntsetTrieElem *root = &trie->root;
	IntsetTrieElem *chunk;
	IntsetTrieElem *parent;
	IntsetTrieElem insert;
	int level = trie->root_level;

	if (level == -1)
	{
		trie->root_level = 0;
		root->key = key;
		root->bitmap = val.bitmap;
		root->p.val = val.val;
		return;
	}

	Assert(root->key <= STARTN(key, level));
	Assert(trie->root_level != 0 || root->key < key);

	/* Adjust root level */
	while (root->key != STARTN(key, level))
	{
		trie->l[level][0] = *root;
		trie->n[level] = 1;
		root->p.children = trie->l[level];
		root->bitmap = BIT(root->key);
		root->key >>= SHIFT;
		level++;
	}
	trie->root_level = level;

	/* Actual insert */
	insert.key = key;
	insert.bitmap = val.bitmap;
	insert.p.val = val.val;

	/*
	 * Iterate while we need to move current level to alloced
	 * space.
	 *
	 * Since we've fixed root in the loop above, we certainly
	 * will quit.
	 */
	for (level = 0;; level++) {
		IntsetTrieElem *alloced;
		uint32 n = trie->n[level];
		Size asize;

		chunk = trie->l[level];
		Assert(chunk[n-1].key <= insert.key);

		if (level < trie->root_level-1)
			parent = &trie->l[level+1][trie->n[level+1]-1];
		else
			parent = root;

		Assert(pg_popcountW(parent->bitmap) == n);

		if (parent->key == START(insert.key))
			/* Yes, we are in the same chunk */
			break;

		/*
		 * We are not in the same chunk. We need to move
		 * layer to allocated space and start new one.
		 */
		asize = n * sizeof(IntsetTrieElem);
		alloced = trie->alloc(asize, trie->alloc_arg);
		memmove(alloced, chunk, asize);
		parent->p.children = alloced;

		/* insert into this level */
		memset(chunk, 0, sizeof(*chunk) * BITS_PER_BITMAPWORD);
		chunk[0] = insert;
		trie->n[level] = 1;

		/* prepare insertion into upper level */
		insert.bitmap = BIT(insert.key);
		insert.p.children = chunk;
		insert.key >>= SHIFT;
	}

	Assert((parent->bitmap & BIT(insert.key)) == 0);

	parent->bitmap |= BIT(insert.key);
	chunk[trie->n[level]] = insert;
	trie->n[level]++;

	Assert(pg_popcountW(parent->bitmap) == trie->n[level]);
}

static IntsetTrieVal
intset2_trie_lookup(IntsetTrie *trie, uint64 key)
{
	IntsetTrieVal	result = {0, NULL};
	IntsetTrieElem *current = &trie->root;
	int level = trie->root_level;

	if (level == -1)
		return result;

	/* root is out of bound */
	if (current->key != STARTN(key, level))
		return result;

	for (; level > 0; level--)
	{
		int n;
		uint64 bit = BITN(key, level);

		if ((current->bitmap & bit) == 0)
			/* Not found */
			return result;
		n = pg_popcountW(current->bitmap & (bit-1));
		current = &current->p.children[n];
	}

	Assert(current->key == key);

	result.bitmap = current->bitmap;
	result.val = current->p.val;

	return result;
}

/* Intset */

/* returns 1 if new element were added, 0 otherwise */
static uint8
intset2_leafbuilder_add(IntsetLeafBuilder *leaf, uint64 v)
{
	uint16	bv;
	uint8	lbyte, lbit, missing;

	bv = v % LEAF_BITS;
	lbyte = LBYTE(bv);
	lbit = LBIT(bv);

	if (leaf->nvals < 3)
		leaf->embed[leaf->nvals] = bv;
	if (leaf->nvals == 0)
		leaf->minbyte = leaf->maxbyte = lbyte;
	else
	{
		Assert(lbyte >= leaf->maxbyte);
		leaf->maxbyte = lbyte;
	}

	lbyte -= leaf->minbyte;

	missing = (leaf->bytes[lbyte] & lbit) == 0;
	leaf->bytes[lbyte] |= lbit;
	leaf->nvals += missing;
	return missing;
}

static inline bool
intset2_leafbuilder_is_member(IntsetLeafBuilder *leaf, uint64 v)
{
	uint16	bv;
	uint8	lbyte, lbit;

	bv = v % LEAF_BITS;
	lbyte = LBYTE(bv);
	lbit = LBIT(bv);

	/* we shouldn't be here unless we set something */
	Assert(leaf->nvals != 0);

	if (lbyte < leaf->minbyte || lbyte > leaf->maxbyte)
		return false;
	lbyte -= leaf->minbyte;
	return (leaf->bytes[lbyte] & lbit) != 0;
}

static uint8
intset2_chunkbuilder_add(IntsetChunkBuilder *chunk, uint64 v)
{
	IntsetLeafBuilder *leafs = chunk->leafs;

	Assert(CSTART(v) == chunk->chunk);
	chunk->bitmap |= (bitmapword)1<<CPOS(v);
	return intset2_leafbuilder_add(&leafs[CPOS(v)], v);
}

static bool
intset2_chunkbuilder_is_member(IntsetChunkBuilder *chunk, uint64 v)
{
	IntsetLeafBuilder *leafs = chunk->leafs;

	Assert(CSTART(v) == chunk->chunk);
	if ((chunk->bitmap & ((bitmapword)1<<CPOS(v))) == 0)
		return false;
	return intset2_leafbuilder_is_member(&leafs[CPOS(v)], v);
}

static bool
intset2_chunk_is_member(IntsetChunk *chunk, bitmapword bitmap, uint64 v)
{
	IntsetLeafHeader	h;

	uint32	cpos;
	bitmapword	cbit;
	uint8	*buf;
	uint32	bv;
	uint8	root;
	uint8	lbyte;
	uint8	l1bm;
	uint8	l1len;
	uint8	l1pos;
	uint8	lbit;
	bool	found;
	bool	inverse;

	cpos = CPOS(v);
	cbit = ONE << cpos;

	if ((bitmap & cbit) == 0)
		return false;
	h = chunk[pg_popcountW(bitmap & (cbit-1))];

	bv = v % LEAF_BITS;
	if (h.e.type == LT_EMBED)
		return bv == h.e.v0 || bv == h.e.v1 || bv == h.e.v2;

	lbyte = LBYTE(bv);
	lbit = LBIT(bv);
	buf = (uint8*)(chunk + pg_popcountW(bitmap)) + h.b.offset;

	if (lbyte < h.b.minbyte || lbyte > h.b.maxbyte)
		return false;
	lbyte -= h.b.minbyte;

	if (h.b.type == LT_RAW)
		return (buf[lbyte] & lbit) != 0;

	inverse = h.b.type == LT_INVERSE;

	/*
	 * Bitmap is sparse, so we have to recalculate lbyte.
	 * lbyte = popcount(bits in level1 up to lbyte)
	 */
	root = buf[0];
	if ((root & (1<<(lbyte/8))) == 0)
		return inverse;

	/* Calculate position in sparse level1 index. */
	l1pos = pg_popcount8_lowbits(root, lbyte/8);
	l1bm = buf[1+l1pos];
	if ((l1bm & (1<<(lbyte&7))) == 0)
		return inverse;
	/* Now we have to check bitmap byte itself */
	/* Calculate length of sparse level1 index */
	l1len = pg_popcount8(root);
	/*
	 * Corrected lbyte position is count of bits set in the level1 upto
	 * our original position.
	 */
	lbyte = pg_popcount_small(buf+1, l1pos) +
			pg_popcount8_lowbits(l1bm, lbyte&7);
	found = (buf[1+l1len+lbyte] & lbit) != 0;
	return found != inverse;
}

IntegerSet2*
intset2_create(void)
{
	IntegerSet2 *intset = palloc0(sizeof(IntegerSet2));

	intset2_trie_init(&intset->trie,
			(trie_alloc)intset2_alloc,
			&intset->alloc);

	return intset;
}

void
intset2_free(IntegerSet2 *intset)
{
	intset2_alloc_free(&intset->alloc);
	pfree(intset);
}

void
intset2_add_member(IntegerSet2 *intset, uint64 v)
{
	uint64 cstart;
	if (intset->nvalues == 0)
	{
		uint8 add;

		intset->firstvalue = CSTART(v);
		v -= intset->firstvalue;
		add = intset2_chunkbuilder_add(&intset->current, v);
		Assert(add == 1);
		intset->nvalues += add;
		return;
	}

	v -= intset->firstvalue;
	cstart = CSTART(v);
	Assert(cstart >= intset->current.chunk);
	if (cstart != intset->current.chunk)
	{
		intset2_compress_current(intset);
		intset->current.chunk = cstart;
	}

	intset->nvalues += intset2_chunkbuilder_add(&intset->current, v);
}

bool
intset2_is_member(IntegerSet2 *intset, uint64 v)
{
	IntsetTrieVal trieval;

	if (intset->nvalues == 0)
		return false;

	if (v < intset->firstvalue)
		return false;

	v -= intset->firstvalue;

	if (intset->current.chunk < CSTART(v))
		return false;

	if (intset->current.chunk == CSTART(v))
		return intset2_chunkbuilder_is_member(&intset->current, v);

	trieval = intset2_trie_lookup(&intset->trie, v>>CHUNK_SHIFT);
	return intset2_chunk_is_member(trieval.val, trieval.bitmap, v);
}

uint64
intset2_num_entries(IntegerSet2 *intset)
{
	return intset->nvalues;
}

uint64
intset2_memory_usage(IntegerSet2 *intset)
{
	/* we are missing alloc->chunks here */
	return sizeof(IntegerSet2) + intset->alloc.total_size;
}

static void
intset2_compress_current(IntegerSet2 *intset)
{
	IntsetChunkBuilder *bld = &intset->current;
	IntsetLeafBuilder *leaf;
	uint32 nheaders = 0;
	IntsetLeafHeader headers[BITS_PER_BITMAPWORD];
	IntsetLeafHeader h = {.v = 0};
	IntsetTrieVal    trieval = {0, NULL};
	uint64  triekey;
	uint32	hlen, totallen;
	uint32	bufpos = 0;
	uint32	i;
	uint8	buffer[BITS_PER_BITMAPWORD * LEAF_BYTES];

	for (i = 0; i < BITS_PER_BITMAPWORD; i++)
	{
		if ((bld->bitmap & (ONE<<i)) == 0)
			continue;

		leaf = &bld->leafs[i];
		Assert(leaf->nvals != 0);

		if (leaf->nvals < 3)
		{
			h.e.type = LT_EMBED;
			/*
			 * Header elements should be all filled because we doesn't store
			 * their amount;
			 * do the trick to fill possibly empty place
			 * n = 1 => n/2 = 0, n-1 = 0
			 * n = 2 => n/2 = 1, n-1 = 1
			 * n = 3 => n/2 = 1, n-1 = 2
			 */
			h.e.v0 = leaf->embed[0];
			h.e.v1 = leaf->embed[leaf->nvals/2];
			h.e.v2 = leaf->embed[leaf->nvals-1];
		}
		else
		{
			/* root raw and root inverse */
			uint8	rraw = 0,
					rinv = 0;
			/* level 1 index raw and index inverse */
			uint8	raw[LEAF_BYTES/8] = {0},
					inv[LEAF_BYTES/8] = {0};
			/* zero count for raw map and inverse map */
			uint8	cnt_00 = 0,
					cnt_ff = 0;
			uint8	mlen, llen;
			uint8   splen, invlen, threshold;
			uint8	b00, bff;
			uint8  *buf;
			int j;

			h.b.minbyte = leaf->minbyte;
			h.b.maxbyte = leaf->maxbyte;
			h.b.offset = bufpos;

			mlen = leaf->maxbyte+1 - leaf->minbyte;
			for (j = 0; j < mlen; j++)
			{
				b00 = leaf->bytes[j] == 0;
				bff = leaf->bytes[j] == 0xff;
				cnt_00 += b00;
				cnt_ff += bff;
				raw[j/8] |= (1-b00) << (j&7);
				inv[j/8] |= (1-bff) << (j&7);
				Assert(j/64 == 0);
				rraw |= (1-b00) << ((j/8)&7);
				rinv |= (1-bff) << ((j/8)&7);
			}

			llen = (mlen-1)/8+1;
			for (j = 0; j < llen; j++)
			{
				cnt_00 += raw[j] == 0;
				cnt_ff += inv[j] == 0;
			}

			buf = buffer + bufpos;

			splen = mlen + llen + 1 - cnt_00;
			invlen = mlen + llen + 1 - cnt_ff;
			threshold = mlen <= 4 ? 0 : /* don't compress */
						mlen <= 8 ? mlen - 2 :
									mlen * 3 / 4;

			/* sparse map compresses well */
			if (splen <= threshold && splen <= invlen)
			{
				h.b.type = LT_SPARSE;
				*buf++ = rraw;
				buf += intset2_compact(buf, raw, llen, false);
				buf += intset2_compact(buf, leaf->bytes, mlen, false);
			}
			/* inverse sparse map compresses well */
			else if (invlen <= threshold)
			{
				h.b.type = LT_INVERSE;
				*buf++ = rinv;
				buf += intset2_compact(buf, inv, llen, false);
				buf += intset2_compact(buf, leaf->bytes, mlen, true);
			}
			/* fallback to raw type */
			else
			{
				h.b.type = LT_RAW;
				memmove(buf, leaf->bytes, mlen);
				buf += mlen;
			}

			bufpos = buf - buffer;
		}
		headers[nheaders] = h;
		nheaders++;
	}

	hlen = nheaders * sizeof(h);
	totallen = hlen + bufpos;

	trieval.bitmap = bld->bitmap;
	trieval.val = intset2_alloc(totallen, &intset->alloc);
	memmove(trieval.val, headers, hlen);
	memmove((char*)trieval.val + hlen, buffer, bufpos);

	triekey = bld->chunk >> CHUNK_SHIFT;
	intset2_trie_insert(&intset->trie, triekey, trieval);

	memset(&intset->current, 0, sizeof(intset->current));
}

#define EXPECT_TRUE(expr)	\
	do { \
		Assert(expr); \
		if (!(expr)) \
			elog(ERROR, \
				 "%s was unexpectedly false in file \"%s\" line %u", \
				 #expr, __FILE__, __LINE__); \
	} while (0)

#define EXPECT_FALSE(expr)	\
	do { \
		Assert(!(expr)); \
		if (expr) \
			elog(ERROR, \
				 "%s was unexpectedly true in file \"%s\" line %u", \
				 #expr, __FILE__, __LINE__); \
	} while (0)

#define EXPECT_EQ_U32(result_expr, expected_expr)	\
	do { \
		uint32		result = (result_expr); \
		uint32		expected = (expected_expr); \
		Assert(result == expected); \
		if (result != expected) \
			elog(ERROR, \
				 "%s yielded %u, expected %s in file \"%s\" line %u", \
				 #result_expr, result, #expected_expr, __FILE__, __LINE__); \
	} while (0)

static void
intset2_test_1_off(uint64 off)
{
	IntegerSet2 *intset;
	uint64 i, d, v;

	intset = intset2_create();

#define K 799

	for (i = 0, d = 1; d < (ONE << (CHUNK_SHIFT + SHIFT + 1)); i+=(d=1+i/K))
	{
		v = i + off;
		EXPECT_FALSE(intset2_is_member(intset, v));
		EXPECT_FALSE(intset2_is_member(intset, v+1));
		if (i != 0)
		{
			EXPECT_TRUE(intset2_is_member(intset, v-d));
		}
		if (d > 1)
		{
			EXPECT_FALSE(intset2_is_member(intset, v-1));
			EXPECT_FALSE(intset2_is_member(intset, v-(d-1)));
		}
		intset2_add_member(intset, v);
		EXPECT_TRUE(intset2_is_member(intset, v));
		if (i != 0)
		{
			EXPECT_TRUE(intset2_is_member(intset, v-d));
		}
		if (d > 1)
		{
			EXPECT_FALSE(intset2_is_member(intset, v-1));
			EXPECT_FALSE(intset2_is_member(intset, v-(d-1)));
		}
		EXPECT_FALSE(intset2_is_member(intset, v+1));
	}

	for (i = 0, d = 0; d < (1 << (CHUNK_SHIFT + SHIFT + 1)); i+=(d=1+i/K))
	{
		v = i + off;

		EXPECT_TRUE(intset2_is_member(intset, v));
		if (d != 0)
		{
			EXPECT_TRUE(intset2_is_member(intset, v-d));
		}
		if (d > 1)
		{
			EXPECT_FALSE(intset2_is_member(intset, v+1));
			EXPECT_FALSE(intset2_is_member(intset, v-1));
			EXPECT_FALSE(intset2_is_member(intset, v-(d-1)));
		}
	}

	intset2_free(intset);
}

void
intset2_test_1(void)
{
	intset2_test_1_off(0);
	intset2_test_1_off(1001);
	intset2_test_1_off(10000001);
	intset2_test_1_off(100000000001);
}

/* Tools */

static inline uint32
intset2_compact(uint8 *dest, uint8 *src, uint8 len, bool inverse)
{
	uint32	i, j;
	uint8	b;

	for (i = j = 0; i < len; i++)
	{
		b = inverse ? ~src[i] : src[i];
		dest[j] = b;
		j += b != 0;
	}

	return j;
}

static const uint8 popcnt[256] = {
	0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4,
	1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
	1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
	2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
	1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
	2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
	2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
	3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
	1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
	2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
	2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
	3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
	2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
	3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
	3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
	4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8
};

static inline uint8
pg_popcount8(uint8 b)
{
	return popcnt[b];
}

static inline uint8
pg_popcount8_lowbits(uint8 b, uint8 nbits)
{
	Assert(nbits < 8);
	return popcnt[b&((1<<nbits)-1)];
}

static inline uint8
pg_popcount_small(uint8 *b, uint8 len)
{
	uint8 r = 0;
	switch (len&7)
	{
		case 7:	r += popcnt[b[6]]; /* fallthrough */
		case 6:	r += popcnt[b[5]]; /* fallthrough */
		case 5:	r += popcnt[b[4]]; /* fallthrough */
		case 4:	r += popcnt[b[3]]; /* fallthrough */
		case 3:	r += popcnt[b[2]]; /* fallthrough */
		case 2:	r += popcnt[b[1]]; /* fallthrough */
		case 1:	r += popcnt[b[0]]; /* fallthrough */
	}
	return r;
}

