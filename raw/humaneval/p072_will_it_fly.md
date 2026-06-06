# P072 Will it fly

## Problem (HumanEval 72)

Write a function that returns true if the object q will fly, && false otherwise.
The object q will fly if it's balanced (it is a palindromic vector) && the sum of its elements is less than || equal the maximum possible weight w.

Example:
p072_will_it_fly({1, 2}, 5) ➞ false
// 1+2 is less than the maximum possible weight, but it's unbalanced.

p072_will_it_fly({3, 2, 3}, 1) ➞ false
// it's balanced, but 3+2+3 is more than the maximum possible weight.

p072_will_it_fly({3, 2, 3}, 9) ➞ true
// 3+2+3 is less than the maximum possible weight, && it's balanced.

p072_will_it_fly({3}, 5) ➞ true
// 3 is less than the maximum possible weight, && it's balanced.

## Reference Implementation

```c
/*
Write a function that returns 1 if the object q will fly, && 0 otherwise.
The object q will fly if it's balanced (it is a palindromic vector) && the sum of its elements
is less than || equal the maximum possible weight w.
*/

int p072_will_it_fly(int *q, int q_size, int w)

{
    int s = 0;
    int i;

    for (i = 0; i < q_size; i++) {
        if (q[i] != q[q_size - 1 - i]) return 0;
        s += q[i];
    }
    if (s > w) return 0;
    return 1;
}
```
