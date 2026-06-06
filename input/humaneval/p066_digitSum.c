/*
Task
Write a function that takes a string as input && returns the sum of the upper characters only's
ASCII codes.

Examples:
    p066_digitSum("") => 0
    p066_digitSum("abAB") => 131
    p066_digitSum("abcCd") => 67
    p066_digitSum("helloE") => 69
    p066_digitSum("woArBld") => 131
    p066_digitSum("aAaaaXa") => 153
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_66_pre: list Z -> Prop)
               (problem_66_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (sum_upper_upto: Z -> list Z -> Z)
               (digit_sum_int_range: list Z -> Prop) */
/*@ Import Coq Require Import p066_digitSum */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int p066_digitSum(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_66_pre(l) &&
        ascii_range(l) &&
        digit_sum_int_range(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_66_spec(l, __return) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int sum = 0;
    int n = strlen(s);
    int i;

    for (i = 0; i < n; i++) {
        if (s[i] >= 65 && s[i] <= 90) {
            sum = sum + s[i];
        }
    }
    return sum;
}
