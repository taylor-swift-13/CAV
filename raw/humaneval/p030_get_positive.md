# P030 Get positive

## Problem (HumanEval 30)

Return only positive numbers in the vector.
>>> p030_get_positive({-1, 2, -4, 5, 6})
{2, 5, 6}
>>> p030_get_positive({5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10})
{5, 3, 2, 3, 9, 123, 1}

## Reference Implementation

```c
typedef struct {
    float* data;
    int size;
} FloatArray;

FloatArray p030_get_positive(const float* l, int l_size){
    FloatArray out;
    out.size = 0;
    out.data = (float*)malloc((size_t)l_size * sizeof(float));
    if (out.data == NULL) {
        return out;
    }
    for (int i=0;i<l_size;i++)
        if (l[i]>0) out.data[out.size++] = l[i];
    return out;
}
```
