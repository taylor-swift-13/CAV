# Generate Integers 163

## Problem (HumanEval 163)

Given two positive integers a && b, return the even digits between a
&& b, in ascending order.

For example:
generate_integers_163(2, 8) => {2, 4, 6, 8}
generate_integers_163(8, 2) => {2, 4, 6, 8}
generate_integers_163(10, 14) => {}

## Reference Implementation

```c
typedef struct {
    int* data;
    int size;
} IntArray;

IntArray generate_integers_163(int a,int b){
    int m;
    IntArray out;
    out.data = NULL;
    out.size = 0;
    if (b<a)
    {
        m=a;a=b;b=m;
    }

    out.data = (int*)malloc((size_t)(b - a + 1) * sizeof(int));
    if (out.data == NULL) {
        return out;
    }
    for (int i=a;i<=b;i++)
    if (i<10 && i%2==0) out.data[out.size++] = i;
    return out;
}
```
