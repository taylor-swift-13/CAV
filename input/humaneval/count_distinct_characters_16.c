/*
Given a string, find out how many distinct characters (regardless of case) does it consist of
>>> count_distinct_characters_16("xyzXYZ")
3
>>> count_distinct_characters_16("Jerry")
4
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_16_pre: list Z -> Prop)
               (problem_16_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (lower: Z -> Z)
               (lower_seen_state: Z -> Z -> list Z -> Z -> Z -> Prop)
               (count_distinct_lower_upto: Z -> list Z -> Z) */
/*@ Import Coq Require Import count_distinct_characters_16 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int count_distinct_characters_16(char *str)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            problem_16_pre(l) &&
            ascii_range(l) &&
            CharArray::full(str, len + 1, app(l, cons(0, nil)))
    Ensure problem_16_spec(l, __return) &&
           CharArray::full(str, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(str);
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        int c = str[i];
        int seen = 0;
        int j;

        if (c >= 65 && c <= 90) {
            c = c + 32;
        }

        for (j = 0; j < i; j++) {
            int d = str[j];
            if (d >= 65 && d <= 90) {
                d = d + 32;
            }
            if (d == c) {
                seen = 1;
            }
        }

        if (seen == 0) {
            count = count + 1;
        }
    }
    return count;
}
