# P090 Next smallest

## Problem (HumanEval 90)

You are given a vector of integers.
Write a function p090_next_smallest() that returns the 2nd smallest element of the vector.
Return None if there is no such element.

p090_next_smallest({1, 2, 3, 4, 5}) == 2
p090_next_smallest({5, 1, 4, 3, 2}) == 2
p090_next_smallest({}) == None
p090_next_smallest({1, 1}) == None

## Reference Implementation

```c
/*
You are given a vector of integers.
Write a function p090_next_smallest() that returns the 2nd smallest element of the vector.
Return None if there is no such element.

p090_next_smallest({1, 2, 3, 4, 5}) == 2
p090_next_smallest({5, 1, 4, 3, 2}) == 2
p090_next_smallest({}) == None
p090_next_smallest({1, 1}) == None
*/

void sort_int_array(int *array, int init_size, int size, int ascending)
;

int p090_next_smallest(int *lst, int lst_size)

{
    int i;

    if (lst_size <= 1) {
        return -1;
    }

    sort_int_array(lst, lst_size, lst_size, 1);

    for (i = 1; i < lst_size; i++) {
        if (lst[i] != lst[i - 1]) {
            return lst[i];
        }
    }
    return -1;
}
```
