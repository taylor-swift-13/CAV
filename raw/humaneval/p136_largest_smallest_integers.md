# P136 Largest smallest integers

## Problem (HumanEval 136)

Create a function that returns a vector (a, b), where "a" is
the largest of negative integers, && "b" is the smallest
of positive integers in a vector.
If there is no negative || positive integers, return them as 0.

Examples:
p136_largest_smallest_integers({2, 4, 1, 3, 5, 7}) == {0, 1}
p136_largest_smallest_integers({}) == {0,0}
p136_largest_smallest_integers({0}) == {0,0}

## Reference Implementation

```c
/*
Create a function that returns a vector (a, b), where "a" is
the largest of negative integers, && "b" is the smallest
of positive integers in a vector.
If there is no negative || positive integers, return them as 0.

Examples:
p136_largest_smallest_integers({2, 4, 1, 3, 5, 7}) == {0, 1}
p136_largest_smallest_integers({}) == {0,0}
p136_largest_smallest_integers({0}) == {0,0}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p136_largest_smallest_integers(int* lst, int lst_size)

{
    int maxneg = 0, minpos = 0;
    int i;

    for (i = 0; i < lst_size; i++)
    {
        if (lst[i] < 0 && (maxneg == 0 || lst[i] > maxneg)) maxneg = lst[i];
        if (lst[i] > 0 && (minpos == 0 || lst[i] < minpos)) minpos = lst[i];
    }
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    data[0] = maxneg;
    data[1] = minpos;
    return out;
}
```
