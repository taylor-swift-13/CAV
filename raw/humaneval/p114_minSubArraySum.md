# P114 MinSubArraySum

## Problem (HumanEval 114)

Given a vector of integers nums, find the minimum sum of any non-empty sub-vector
of nums.
Example
p114_minSubArraySum({2, 3, 4, 1, 2, 4}) == 1
p114_minSubArraySum({-1, -2, -3}) == -6

## Reference Implementation

```c
/*
Given a vector of integers nums, find the minimum sum of any non-empty sub-vector
of nums.
Example
p114_minSubArraySum({2, 3, 4, 1, 2, 4}) == 1
p114_minSubArraySum({-1, -2, -3}) == -6
*/

long long p114_minSubArraySum(long long* nums, int nums_size)

{
    long long current,min;
    current=nums[0];
    min=nums[0];

    for (int i=1;i<nums_size;i++)
    {
       if (current<0) current=current+nums[i];
       else current=nums[i];
       if (current<min) min=current;
    }
    return min;
}
```
