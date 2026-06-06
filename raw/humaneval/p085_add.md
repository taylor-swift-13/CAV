# P085 Add

## Problem (HumanEval 85)

Given a non-empty vector of integers lst. p085_add the even elements that are at odd indices..


Examples:
    p085_add({4, 2, 6, 7}) ==> 2

## Reference Implementation

```c
/*
Given a non-empty vector of integers lst. p085_add the even elements that are at odd indices.

Examples:
    p085_add({4, 2, 6, 7}) ==> 2
*/

int p085_add(int *lst, int lst_size)

{
    int s = 0;
    int i;

    for (i = 0; i * 2 + 1 < lst_size; i++)
        if (lst[i * 2 + 1] % 2 == 0) s += lst[i * 2 + 1];
    return s;
}
```
