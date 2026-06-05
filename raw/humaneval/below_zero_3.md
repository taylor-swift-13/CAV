# Below Zero 3

## Problem (HumanEval 3)

You"re given a vector of deposit && withdrawal operations on a bank account that starts with
zero balance. Your task is to detect if at any point the balance of account falls below zero, &&
at that point function should return true. Otherwise it should return false.
>>> below_zero_3({1, 2, 3})
false
>>> below_zero_3({1, 2, -4, 5})
true

## Reference Implementation

```c
bool below_zero_3(int* operations, int operations_size){
    int num=0;
    for (int i=0;i<operations_size;i++)
    {
        num+=operations[i];
        if (num<0) return true;
    }
    return false;
}
```
