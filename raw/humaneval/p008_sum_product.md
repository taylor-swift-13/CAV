# P008 Sum product

## Problem (HumanEval 8)

For a given vector of integers, return a vector consisting of a sum && a product of all the integers in a vector.
Empty sum should be equal to 0 && empty product should be equal to 1.
>>> p008_sum_product({})
(0, 1)
>>> p008_sum_product({1, 2, 3, 4})
(10, 24)

## Reference Implementation

```c
/*
For a given vector of integers, return a vector consisting of a sum && a product of all the integers in a vector.
Empty sum should be equal to 0 && empty product should be equal to 1.
>>> p008_sum_product({})
(0, 1)
>>> p008_sum_product({1, 2, 3, 4})
(10, 24)
*/

int *malloc_int_array(int size)
;

int *p008_sum_product(int *numbers, int numbers_size)

{
    int sum = 0;
    int product = 1;
    int i;
    int *out = malloc_int_array(2);

    for (i = 0; i < numbers_size; i++) {
        sum += numbers[i];
        product *= numbers[i];
    }

    out[0] = sum;
    out[1] = product;
    return out;
}
```
