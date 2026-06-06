/*
Write a function that takes an array of numbers as input and returns
the number of elements in the array that are greater than 10 and both
first and last digits of a number are odd (1, 3, 5, 7, 9).
For example:
specialFilter_146([15, -73, 14, -15]) => 1
specialFilter_146([33, -2, -3, 45, 21, 109]) => 2
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_146_pre: list Z -> Prop)
               (problem_146_spec: list Z -> Z -> Prop)
               (special_filter_prefix: Z -> list Z -> Z -> Prop)
               (special_filter_int_range: list Z -> Prop)
               (first_digit_state: Z -> Z -> Prop)
               (special_number_c: Z -> Prop)
               (not_special_number_c: Z -> Prop) */
/*@ Import Coq Require Import specialFilter_146 */

int specialFilter_146(int* nums, int nums_size)
/*@ With input_l
    Require
        0 <= nums_size && nums_size < INT_MAX &&
        nums_size == Zlength(input_l) &&
        problem_146_pre(input_l) &&
        special_filter_int_range(input_l) &&
        IntArray::full(nums, nums_size, input_l)
    Ensure
        problem_146_spec(input_l, __return) &&
        IntArray::full(nums, nums_size, input_l)
*/
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
