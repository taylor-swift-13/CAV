# Sum Product 8

## Problem (HumanEval 8)

For a given vector of integers, return a vector consisting of a sum && a product of all the integers in a vector.
Empty sum should be equal to 0 && empty product should be equal to 1.
>>> sum_product_8({})
(0, 1)
>>> sum_product_8({1, 2, 3, 4})
(10, 24)

## Reference Implementation

```c
typedef struct {
    int* data;
    int size;
} IntArray;

IntArray sum_product_8(const int* numbers, int numbers_size){
    int sum=0,product=1;
    IntArray out;
    out.data = (int*)malloc(2 * sizeof(int));
    out.size = 2;

    if (out.data == NULL) {
        out.size = 0;
        return out;
    }

    for (int i=0;i<numbers_size;i++)
    {
        sum+=numbers[i];
        product*=numbers[i];
    }
    out.data[0] = sum;
    out.data[1] = product;
    return out;
}
```
