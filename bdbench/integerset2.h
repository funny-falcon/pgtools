#ifndef INTEGERSET2_H
#define INTEGERSET2_H

typedef struct IntegerSet2 IntegerSet2;

extern IntegerSet2 *intset2_create(void);
extern void intset2_free(IntegerSet2 *intset);
extern void intset2_add_member(IntegerSet2 *intset, uint64 x);
extern bool intset2_is_member(IntegerSet2 *intset, uint64 x);

extern uint64 intset2_num_entries(IntegerSet2 *intset);
extern uint64 intset2_memory_usage(IntegerSet2 *intset);

extern void intset2_test_1(void);
#endif  /* INTEGERSET2_H */
