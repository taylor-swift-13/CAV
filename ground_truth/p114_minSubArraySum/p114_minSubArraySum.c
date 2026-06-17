/*
Given a vector of integers nums, find the minimum sum of any non-empty sub-vector
of nums.
Example
p114_minSubArraySum({2, 3, 4, 1, 2, 4}) == 1
p114_minSubArraySum({-1, -2, -3}) == -6
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "long_array_def.h"

/*@ Extern Coq (problem_114_pre: list Z -> Prop)
               (problem_114_spec: list Z -> Z -> Prop)
               (min_suffix_prefix: Z -> list Z -> Z)
               (min_subarray_prefix: Z -> list Z -> Z)
               (kadane_int64_range: list Z -> Prop) */
/*@ Import Coq Require Import p114_minSubArraySum */

long long p114_minSubArraySum(long long* nums, int nums_size)
/*@ With nums_l
    Require
        1 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(nums_l) &&
        problem_114_pre(nums_l) &&
        kadane_int64_range(nums_l) &&
        LongArray::full(nums, nums_size, nums_l)
    Ensure
        problem_114_spec(nums_l, __return) &&
        LongArray::full(nums, nums_size, nums_l)
*/
{
    long long current,min;
    current=nums[0];
    min=nums[0];
    /*@ Inv Assert
        nums == nums@pre &&
        nums_size == nums_size@pre &&
        1 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(nums_l) &&
        problem_114_pre(nums_l) &&
        kadane_int64_range(nums_l) &&
        1 <= i && i <= nums_size &&
        current == min_suffix_prefix(i, nums_l) &&
        min == min_subarray_prefix(i, nums_l) &&
        LongArray::full(nums, nums_size, nums_l)
    */
    for (int i=1;i<nums_size;i++)
    {
       if (current<0) current=current+nums[i];
       else current=nums[i];
       if (current<min) min=current;
    }
    return min;
}
