/*
Write a function p108_count_nums which takes a vector of integers && returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, && 3.
>>> p108_count_nums({}) == 0
>>> p108_count_nums({-1, 11, -11}) == 1
>>> p108_count_nums({1, 1, 2}) == 3
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs: Z -> Z)
               (problem_108_pre: list Z -> Prop)
               (problem_108_spec: list Z -> Z -> Prop)
               (count_nums_prefix: Z -> list Z -> Z -> Prop)
               (count_nums_int_range: list Z -> Prop)
               (digit_scan_state: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p108_count_nums */

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) {
        return -x;
    }
    else {
        return x;
    }
}

int p108_count_nums(int* n, int n_size)
/*@ With input_l
    Require
        0 <= n_size && n_size < INT_MAX &&
        n_size == Zlength(input_l) &&
        problem_108_pre(input_l) &&
        count_nums_int_range(input_l) &&
        IntArray::full(n, n_size, input_l)
    Ensure
        problem_108_spec(input_l, __return) &&
        IntArray::full(n, n_size, input_l)
*/
{
    int num=0;
    int i;

    for (i=0;i<n_size;i++) {
        if (n[i]>0) {
            num+=1;
        }
        else
        {
            int sum=0;
            int w;
            w=abs(n[i]);

            while (w>=10)
            {
                sum+=w%10;
                w=w/10;
            }
            sum-=w;
            if (sum>0) {
                num+=1;
            }
        }
    }
    return num;
}
