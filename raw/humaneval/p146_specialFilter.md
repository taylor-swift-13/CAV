# P146 SpecialFilter

## Problem (HumanEval 146)

Write a function that takes a vector of numbers as input && returns
the number of elements in the vector that are greater than 10 && both
first && last digits of a number are odd (1, 3, 5, 7, 9).
For example:
p146_specialFilter({15, -73, 14, -15}) => 1
p146_specialFilter({33, -2, -3, 45, 21, 109}) => 2

## Reference Implementation

```c
/*
Write a function that takes an array of numbers as input and returns
the number of elements in the array that are greater than 10 and both
first and last digits of a number are odd (1, 3, 5, 7, 9).
For example:
p146_specialFilter([15, -73, 14, -15]) => 1
p146_specialFilter([33, -2, -3, 45, 21, 109]) => 2
*/

int p146_specialFilter(int* nums, int nums_size)

{
    int num=0;
    int i;

    for (i=0;i<nums_size;i++) {
        if (nums[i]>10)
        {
            int first;
            int last;
            first = nums[i];
            last = nums[i] % 10;

            while (first >= 10) {
                first /= 10;
            }
            if (first % 2 == 1 && last % 2 == 1) {

                num+=1;
            }

        }

    }
    return num;
}
```
