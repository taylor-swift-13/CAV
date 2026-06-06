# P052 Below threshold

## Problem (HumanEval 52)

Return true if all numbers in the vector l are below threshold t.
>>> p052_below_threshold({1, 2, 4, 10}, 100)
true
>>> p052_below_threshold({1, 20, 4, 10}, 5)
false

## Reference Implementation

```c
/*
Return 1 if all numbers in the vector l are below threshold t, 0 otherwise.
>>> p052_below_threshold({1, 2, 4, 10}, 100)
1
>>> p052_below_threshold({1, 20, 4, 10}, 5)
0
*/

int p052_below_threshold(int *l, int l_size, int t)

{
    int i;

    for (i = 0; i < l_size; i++)
        if (l[i] >= t) return 0;
    return 1;
}
```
