/*
You are given a string s.
Your task is to check if the string is happy || !.
A string is happy if its length is at least 3 && every 3 consecutive letters are distinct
For example:
p080_is_happy("a") => false
p080_is_happy("aa") => false
p080_is_happy("abcd") => true
p080_is_happy("aabb") => false
p080_is_happy("adb") => true
p080_is_happy("xyy") => false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_80_pre: list Z -> Prop)
               (problem_80_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (happy_prefix: Z -> list Z -> Prop)
               (happy_adjacent: Z -> list Z -> Prop) */
/*@ Import Coq Require Import p080_is_happy */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int p080_is_happy(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_80_pre(l) &&
        ascii_range(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_80_spec(l, __return) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(s);
    int i;
    if (n < 3) {
        return 0;
    }
    if (s[0] == s[1]) {
        return 0;
    }

    for (i = 2; i < n; i++) {
        if (s[i] == s[i - 1]) {
            return 0;
        }
        if (s[i] == s[i - 2]) {
            return 0;
        }
    }
    return 1;
}
