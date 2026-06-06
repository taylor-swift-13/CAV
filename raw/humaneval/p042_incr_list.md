# P042 Incr list

## Problem (HumanEval 42)

Return vector with elements incremented by 1.
>>> incr_vector({1, 2, 3})
{2, 3, 4}
>>> incr_vector({5, 3, 5, 2, 3, 3, 9, 0, 123})
{6, 4, 6, 3, 4, 4, 10, 1, 124}

## Reference Implementation

```c
/*
Return vector with elements incremented by 1.
>>> p042_incr_list({1, 2, 3})
{2, 3, 4}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p042_incr_list(int *l, int l_size)

{
    int i;
    IntArray *out = malloc_int_array_struct();
    out->size = l_size;
    out->data = malloc_int_array(l_size);
    int *data = out->data;

    for (i = 0; i < l_size; ++i)
        data[i] = l[i] + 1;
    return out;
}
```
