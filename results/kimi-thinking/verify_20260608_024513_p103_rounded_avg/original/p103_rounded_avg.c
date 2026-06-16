/*
You are given two positive integers n && m, && your task is to compute the
average of the integers from n through m (including n && m).
Round the answer to the nearest integer(smaller one) && convert that to binary.
If n is greater than m, return "-1".
Example:
p103_rounded_avg(1, 5) => "11"
p103_rounded_avg(7, 5) => "-1"
p103_rounded_avg(10, 20) => "1111"
p103_rounded_avg(20, 33) => "11010"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_103_pre: Z -> Z -> Prop)
               (problem_103_spec: Z -> Z -> list Z -> Prop)
               (avg_103: Z -> Z -> Z)
               (binary_digits: Z -> list Z)
               (binary_count_state: Z -> Z -> Z -> Prop)
               (binary_fill_full_state: Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import p103_rounded_avg */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* p103_rounded_avg(int n, int m)
/*@ Require
        0 < n && 0 < m &&
        n < INT_MAX && m < INT_MAX &&
        n + m < INT_MAX &&
        problem_103_pre(n, m)
    Ensure exists out_l len,
        (forall (k: Z), (0 <= k && k < len) => Znth(k, out_l, 0) != 0) &&
        1 <= len && len < INT_MAX &&
        Zlength(out_l) == len &&
        problem_103_spec(n, m, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    if (n > m) {
        char *out_neg = malloc_char_array(3);
        out_neg[0] = 45;
        out_neg[1] = 49;
        out_neg[2] = 0;
        return out_neg;
    } else {
        int num = (n + m) / 2;
        int orig = num;
        int digits = 0;
        int t = num;
        int total = 0;
        int i = 0;
        char *out = 0;

        while (t > 0) {
            digits = digits + 1;
            t = t / 2;
        }

        total = digits;
        out = malloc_char_array(total + 1);

        for (i = 0; i <= total; i++) {
            out[i] = 0;
        }


        while (num > 0) {
            digits = digits - 1;

            out[digits] = 48 + (num % 2);
            num = num / 2;
        }
        return out;
    }
}
