# P126 Is sorted

## Problem (HumanEval 126)

Given a vector of numbers, return whether || ! they are sorted
in ascending order. If vector has more than 1 duplicate of the same
number, return false. Assume no negative numbers && only integers.

Examples
p126_is_sorted({5}) ➞ true
p126_is_sorted({1, 2, 3, 4, 5}) ➞ true
p126_is_sorted({1, 3, 2, 4, 5}) ➞ false
p126_is_sorted({1, 2, 3, 4, 5, 6}) ➞ true
p126_is_sorted({1, 2, 3, 4, 5, 6, 7}) ➞ true
p126_is_sorted({1, 3, 2, 4, 5, 6, 7}) ➞ false
p126_is_sorted({1, 2, 2, 3, 3, 4}) ➞ true
p126_is_sorted({1, 2, 2, 2, 3, 4}) ➞ false

## Reference Implementation

```c
/*
Given a vector of numbers, return whether || ! they are sorted
in ascending order. If vector has more than 1 duplicate of the same
number, return false. Assume no negative numbers && only integers.

Examples
p126_is_sorted({5}) ➞ true
p126_is_sorted({1, 2, 3, 4, 5}) ➞ true
p126_is_sorted({1, 3, 2, 4, 5}) ➞ false
p126_is_sorted({1, 2, 3, 4, 5, 6}) ➞ true
p126_is_sorted({1, 2, 3, 4, 5, 6, 7}) ➞ true
p126_is_sorted({1, 3, 2, 4, 5, 6, 7}) ➞ false
p126_is_sorted({1, 2, 2, 3, 3, 4}) ➞ true
p126_is_sorted({1, 2, 2, 2, 3, 4}) ➞ false
*/

int p126_is_sorted(int* lst, int lst_size)

{

    for (int i=1;i<lst_size;i++)
    {
        if (lst[i]<lst[i-1]) return 0;
        if (i>=2 && lst[i]==lst[i-1] && lst[i]==lst[i-2]) return 0;
    }
    return 1;
}
```
