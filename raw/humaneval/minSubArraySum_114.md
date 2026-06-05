# Minsubarraysum 114

## Problem (HumanEval 114)

Given a vector of integers nums, find the minimum sum of any non-empty sub-vector
of nums.
Example
minSubArraySum_114({2, 3, 4, 1, 2, 4}) == 1
minSubArraySum_114({-1, -2, -3}) == -6

## Reference Implementation

```c
long long minSubArraySum_114(long long* nums, int nums_size){
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
