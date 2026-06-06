# P033 Sort third

## Problem (HumanEval 33)

This function takes a vector l && returns a vector l' such that
l' is identical to l in the indicies that are ! divisible by three, while its values at the indicies that are divisible by three are equal
to the values of the corresponding indicies of l, but sorted.
>>> p033_sort_third({1, 2, 3})
{1, 2, 3}
>>> p033_sort_third({5, 6, 3, 4, 8, 9, 2})
{2, 6, 3, 4, 8, 9, 5}

## Reference Implementation

```c
/*
This function takes a vector l and returns a vector l' such that l' is
identical to l at indices that are not divisible by three, while the values at
indices divisible by three are the corresponding values of l, but sorted.

>>> p033_sort_third({1, 2, 3})
{1, 2, 3}
>>> p033_sort_third({5, 6, 3, 4, 8, 9, 2})
{2, 6, 3, 4, 8, 9, 5}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

void free_int_array(int *array, int size)
;

void sort_int_array(int *array, int init_size, int size, int ascending)
;

IntArray *p033_sort_third(int *l, int l_size)

{
    IntArray *out = malloc_int_array_struct();
    out->size = l_size;
    out->data = malloc_int_array(l_size);
    int *data = out->data;
    int third_size = (l_size + 2) / 3;
    int *third = malloc_int_array(l_size);
    int i;
    int j;

    for (i = 0; i * 3 < l_size; i++)
        third[i] = l[i * 3];

    sort_int_array(third, third_size, l_size, 1);

    j = 0;

    for (i = 0; i < l_size; i++)
    {
        if (i % 3 == 0) { data[i] = third[j]; j = j + 1; }
        else data[i] = l[i];
    }

    free_int_array(third, l_size);
    return out;
}
```
