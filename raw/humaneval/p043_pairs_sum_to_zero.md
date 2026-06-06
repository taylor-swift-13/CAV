# P043 Pairs sum to zero

## Problem (HumanEval 43)

p043_pairs_sum_to_zero takes a vector of integers as an input.
it returns true if there are two distinct elements in the vector that
sum to zero, && false otherwise.
>>> p043_pairs_sum_to_zero({1, 3, 5, 0})
false
>>> p043_pairs_sum_to_zero({1, 3, -2, 1})
false
>>> p043_pairs_sum_to_zero({1, 2, 3, 7})
false
>>> p043_pairs_sum_to_zero({2, 4, -5, 3, 5, 7})
true
>>> p043_pairs_sum_to_zero({1})
false

## Reference Implementation

```c
/*
p043_pairs_sum_to_zero takes a vector of integers as an input.
it returns true if there are two distinct elements in the vector that
sum to zero, && false otherwise.
>>> p043_pairs_sum_to_zero({1, 3, 5, 0})
false
>>> p043_pairs_sum_to_zero({2, 4, -5, 3, 5, 7})
true
*/

int p043_pairs_sum_to_zero(int *l, int l_size)

{
    int i;
    int j;

    for (i = 0; i < l_size; i++) {

        for (j = i + 1; j < l_size; j++)
            if (l[i] + l[j] == 0) return 1;
    }
    return 0;
}
```
