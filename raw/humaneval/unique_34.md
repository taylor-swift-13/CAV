# Unique 34

## Problem (HumanEval 34)

Return sorted unique_34 elements in a vector
>>> unique_34({5, 3, 5, 2, 3, 3, 9, 0, 123})
{0, 2, 3, 5, 9, 123}

## Reference Implementation

```c
typedef struct {
    int* data;
    int size;
} IntArray;

static int cmp_int(const void* a, const void* b) {
    int x = *(const int*)a;
    int y = *(const int*)b;
    return (x > y) - (x < y);
}

static int contains(const int* a, int n, int x) {
    for (int i = 0; i < n; i++) if (a[i] == x) return 1;
    return 0;
}

IntArray unique_34(const int* l, int l_size){
    IntArray out;
    out.size = 0;
    out.data = (int*)malloc((size_t)l_size * sizeof(int));
    if (out.data == NULL) {
        return out;
    }
    for (int i=0;i<l_size;i++)
        if (!contains(out.data, out.size, l[i]))
            out.data[out.size++] = l[i];
    qsort(out.data, (size_t)out.size, sizeof(int), cmp_int);
    return out;
}
```
