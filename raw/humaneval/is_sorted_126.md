# Is Sorted 126

## Problem (HumanEval 126)

Given a vector of numbers, return whether || ! they are sorted
in ascending order. If vector has more than 1 duplicate of the same
number, return false. Assume no negative numbers && only integers.

Examples
is_sorted_126({5}) ➞ true
is_sorted_126({1, 2, 3, 4, 5}) ➞ true
is_sorted_126({1, 3, 2, 4, 5}) ➞ false
is_sorted_126({1, 2, 3, 4, 5, 6}) ➞ true
is_sorted_126({1, 2, 3, 4, 5, 6, 7}) ➞ true
is_sorted_126({1, 3, 2, 4, 5, 6, 7}) ➞ false
is_sorted_126({1, 2, 2, 3, 3, 4}) ➞ true
is_sorted_126({1, 2, 2, 2, 3, 4}) ➞ false

## Reference Implementation

```c
/* TODO: C replacement for <algorithm> */
bool is_sorted_126(int* lst, int lst_size){
    for (int i=1;i<lst_size;i++)
    {
        if (lst[i]<lst[i-1]) return false;
        if (i>=2 && lst[i]==lst[i-1] && lst[i]==lst[i-2]) return false;
    }
    return true;
}
```
