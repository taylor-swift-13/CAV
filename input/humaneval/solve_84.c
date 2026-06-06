/*
Given a positive integer N, return the total sum of its digits in binary.

Example
    For N = 1000, the sum of digits will be 1 the output should be "1".
    For N = 150, the sum of digits will be 6 the output should be "110".
    For N = 147, the sum of digits will be 12 the output should be "1100".

Variables:
    @N integer
         Constraints: 0 <= N <= 10000.
Output:
     a string of binary number
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_84_pre: Z -> Prop)
               (problem_84_spec: Z -> list Z -> Prop)
               (decimal_sum_state: Z -> Z -> Z -> Prop)
               (decimal_sum_value: Z -> Z -> Prop)
               (binary_digits: Z -> list Z)
               (binary_count_state: Z -> Z -> Z -> Prop)
               (binary_fill_full_state: Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import solve_84 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* solve_84(int N)
/*@ Require
        0 <= N && N <= 10000 &&
        problem_84_pre(N)
    Ensure exists out_l len,
        1 <= len && len < INT_MAX &&
        Zlength(out_l) == len &&
        problem_84_spec(N, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    if (N == 0) {
        char *out_zero = malloc_char_array(2);
        out_zero[0] = 48;
        out_zero[1] = 0;
        return out_zero;
    } else {
        int origN = N;
        int x = N;
        int sum = 0;
        int num = 0;
        int orig = 0;
        int bits = 0;
        int t = 0;
        int total = 0;
        int i = 0;
        char *out = 0;

        while (x > 0) {
            sum = sum + (x % 10);
            x = x / 10;
        }

        if (sum == 0) {
            char *out_zero = malloc_char_array(2);
            out_zero[0] = 48;
            out_zero[1] = 0;
            return out_zero;
        }

        num = sum;
        orig = num;
        t = num;

        while (t > 0) {
            bits = bits + 1;
            t = t / 2;
        }

        total = bits;
        out = malloc_char_array(total + 1);

        for (i = 0; i <= total; i++) {
            out[i] = 0;
        }

        
        while (num > 0) {
            bits = bits - 1;
            
            out[bits] = 48 + (num % 2);
            num = num / 2;
        }
        return out;
    }
}
