# P003 Below zero

## Problem (HumanEval 3)

You"re given a vector of deposit && withdrawal operations on a bank account that starts with
zero balance. Your task is to detect if at any point the balance of account falls below zero, &&
at that point function should return true. Otherwise it should return false.
>>> p003_below_zero({1, 2, 3})
false
>>> p003_below_zero({1, 2, -4, 5})
true

## Reference Implementation

```c
int p003_below_zero(int *operations, int operations_size)

{
    int num = 0;
    int i;

    for (i = 0; i < operations_size; i++) {
        num += operations[i];
        if (num < 0) {
            return 1;
        }
    }
    return 0;
}
```
