/*
Find how many times a given substring can be found in the original string. Count overlaping cases.
>>> how_many_times_18("", "a")
0
>>> how_many_times_18("aaa", "a")
3
>>> how_many_times_18("aaaa", "aa")
3
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_18_pre_z: list Z -> list Z -> Prop)
               (problem_18_spec_z: list Z -> list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (match_progress_z: Z -> Z -> Z -> list Z -> list Z -> Prop)
               (count_matches_upto: Z -> list Z -> list Z -> Z) */
/*@ Import Coq Require Import coins_18 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int how_many_times_18(char *str, char *substring)
/*@ With l n sub m
    Require
        0 <= n && n < INT_MAX &&
        0 <= m && m < INT_MAX &&
        Zlength(l) == n &&
        Zlength(sub) == m &&
        problem_18_pre_z(l, sub) &&
        ascii_range_z(l) &&
        ascii_range_z(sub) &&
        CharArray::full(str, n + 1, app(l, cons(0, nil))) *
        CharArray::full(substring, m + 1, app(sub, cons(0, nil)))
    Ensure
        problem_18_spec_z(l, sub, __return) &&
        CharArray::full(str, n + 1, app(l, cons(0, nil))) *
        CharArray::full(substring, m + 1, app(sub, cons(0, nil)))
*/
{
    int out = 0;
    int i = 0;
    int j = 0;
    int ok = 0;
    int n0 = strlen(str) /*@ where l = l, n = n */;
    int m0 = strlen(substring) /*@ where l = sub, n = m */;

    if (n0 == 0) {
        return 0;
    }
    if (m0 == 0) {
        return 0;
    }
    if (m0 > n0) {
        return 0;
    }

    for (i = 0; i <= n0 - m0; i++) {
        ok = 1;

        for (j = 0; j < m0; j++) {
            if (str[i + j] != substring[j]) {
                ok = 0;
            }
        }

        if (ok == 1) {
            out += 1;
        }
    }
    return out;
}
