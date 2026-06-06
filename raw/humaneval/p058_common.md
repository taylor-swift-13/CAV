# P058 Common

## Problem (HumanEval 58)

Return sorted unique p058_common elements for two vectors.
>>> p058_common({1, 4, 3, 34, 653, 2, 5}, {5, 7, 1, 5, 9, 653, 121})
{1, 5, 653}
>>> p058_common({5, 3, 2, 8}, {3, 2})
{2, 3}

## Reference Implementation

```c
/*
Return sorted unique p058_common elements for two vectors.
>>> p058_common({1, 4, 3, 34, 653, 2, 5}, {5, 7, 1, 5, 9, 653, 121})
{1, 5, 653}
>>> p058_common({5, 3, 2, 8}, {3, 2})
{2, 3}

*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

int contains(int *a, int n, int x)

{
    int i;

    for (i = 0; i < n; i++) {
        if (a[i] == x) {
            return 1;
        }
    }
    return 0;
}

void sort_int_array(int *array, int init_size, int size, int ascending)
;

IntArray *p058_common(int *l1, int l1_size, int *l2, int l2_size)

{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(l1_size);
    int *data = out->data;
    int output_size = 0;
    int i;

    for (i = 0; i < l1_size; i++) {
        int current = l1[i];
        int in_output = contains(data, output_size, current);
        if (!in_output) {
            int in_l2 = contains(l2, l2_size, current);
            if (in_l2) {
                data[output_size] = current;
                output_size = output_size + 1;
            }
        }
    }

    sort_int_array(data, output_size, l1_size, 1);
    out->size = output_size;
    return out;
}
```
