# P121 Solutions

## Problem (HumanEval 121)

Given a non-empty vector of integers, return the sum of all of the odd elements that are in even positions.


Examples
solution({5, 8, 7, 1}) ==> 12
solution({3, 3, 3, 3, 3}) ==> 9
solution({30, 13, 24, 321}) ==>0

## Reference Implementation

```c
/*
Given a non-empty vector of integers, return the sum of all of the odd elements
that are in even positions (0-indexed).

Examples:
solution({5, 8, 7, 1}) ==> 12   (5 + 7)
solution({3, 3, 3, 3, 3}) ==> 9
solution({30, 13, 24, 321}) ==> 0
*/

int p121_solutions(int *lst, int lst_size)

{
    int s = 0;
    int i;

    for (i = 0; i * 2 < lst_size; i++)
        if (lst[i * 2] % 2 == 1) s += lst[i * 2];
    return s;
}
```
