/*
Given a string s, count the number of uppercase vowels in even indices.

For example:
p098_count_upper("aBCdEf") returns 1
p098_count_upper("abcdefg") returns 0
p098_count_upper("dBBE") returns 0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_98_pre: list Z -> Prop)
               (problem_98_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (count_upper_even_upto: Z -> list Z -> Z) */
/*@ Import Coq Require Import p098_count_upper */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int p098_count_upper(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_98_pre(l) &&
        ascii_range(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_98_spec(l, __return) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(s);
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (i % 2 == 0) {
            if (s[i] == 65 || s[i] == 69 || s[i] == 73 ||
                s[i] == 79 || s[i] == 85) {
                count = count + 1;
            }
        }
    }
    return count;
}
