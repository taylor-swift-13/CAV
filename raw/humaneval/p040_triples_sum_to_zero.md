# P040 Triples sum to zero

## Problem (HumanEval 40)

p040_triples_sum_to_zero takes a vector of integers as an input.
it returns true if there are three distinct elements in the vector that
sum to zero, && false otherwise.

>>> p040_triples_sum_to_zero({1, 3, 5, 0})
false
>>> p040_triples_sum_to_zero({1, 3, -2, 1})
true
>>> p040_triples_sum_to_zero({1, 2, 3, 7})
false
>>> p040_triples_sum_to_zero({2, 4, -5, 3, 9, 7})
true
>>> p040_triples_sum_to_zero({1})
false

## Reference Implementation

```c
/*
p040_triples_sum_to_zero takes a vector of integers as an input.
it returns true if there are three distinct elements in the vector that
sum to zero, && false otherwise.

>>> p040_triples_sum_to_zero({1, 3, 5, 0})
false
>>> p040_triples_sum_to_zero({1, 3, -2, 1})
true
*/

int p040_triples_sum_to_zero(int *l, int l_size)

{
    int i;
    int j;
    int k;

    for (i = 0; i < l_size; i++) {

        for (j = i + 1; j < l_size; j++) {

            for (k = j + 1; k < l_size; k++)
                if (l[i] + l[j] + l[k] == 0) return 1;
        }
    }
    return 0;
}
```
