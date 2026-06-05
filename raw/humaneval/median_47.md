# Median 47

## Problem (HumanEval 47)

Return median_47 of elements in the vector l.
>>> median_47({3, 1, 2, 4, 5})
3
>>> median_47({-10, 4, 6, 1000, 10, 20})
15.0

## Reference Implementation

```c
static int cmp_float(const void* a, const void* b){
    float fa = *(const float*)a;
    float fb = *(const float*)b;
    return (fa > fb) - (fa < fb);
}

float median_47(float* l, int l_size){
    qsort(l, (size_t)l_size, sizeof(float), cmp_float);
    if (l_size%2==1) return l[l_size/2];
    return 0.5*(l[l_size/2]+l[l_size/2-1]);
}
```
