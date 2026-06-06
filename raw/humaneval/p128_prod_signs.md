# P128 Prod signs

## Problem (HumanEval 128)

You are given a vector arr of integers && you need to return
sum of magnitudes of integers multiplied by product of all signs
of each number in the vector, represented by 1, -1 || 0.
Note: return -32768 for empty arr.

Example:
>>> p128_prod_signs({1, 2, 2, -4}) == -9
>>> p128_prod_signs({0, 1}) == 0
>>> p128_prod_signs({}) == -32768

## Reference Implementation

```c
/*
You are given a vector arr of integers && you need to return
sum of magnitudes of integers multiplied by product of all signs
of each number in the vector, represented by 1, -1 || 0.
Note: return -32768 for empty arr.

Example:
>>> p128_prod_signs({1, 2, 2, -4}) == -9
>>> p128_prod_signs({0, 1}) == 0
>>> p128_prod_signs({}) == -32768
*/

int abs(int x)

{
    if (x < 0) return -x;
    else return x;
}

int p128_prod_signs(int* arr, int arr_size)

{
    if (arr_size == 0) return -32768;
    int i, sum = 0, prods = 1;

    for (i = 0; i < arr_size; i++)
    {
        int current = arr[i];
        int mag = abs(current);

        sum += mag;
        if (current == 0) prods = 0;
        if (current < 0) prods = -prods;
   }
   return sum * prods;
}
```
