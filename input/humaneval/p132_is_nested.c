/*
Create a function that takes a string as input which contains only square brackets.
The function should return true if && only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

p132_is_nested("[[]]") -> true
p132_is_nested("[]]]]]]][[[[[]") -> false
p132_is_nested("[][]") -> false
p132_is_nested("[]") -> false
p132_is_nested("[[][]]") -> true
p132_is_nested("[[]][[") -> true
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_132_pre: list Z -> Prop)
               (problem_132_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (subseq_state_prefix: Z -> list Z -> Z) */
/*@ Import Coq Require Import p132_is_nested */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int p132_is_nested(char *str)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_132_pre(l) &&
        ascii_range(l) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_132_spec(l, __return) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
*/
{
    int state = 0;
    int i;
    int n = strlen(str);

    for (i = 0; i < n; i++) {
        int chr = str[i];
        if (state == 0) {
            if (chr == 91) {
                state = 1;
            }
        } else if (state == 1) {
            if (chr == 91) {
                state = 2;
            }
        } else if (state == 2) {
            if (chr == 93) {
                state = 3;
            }
        } else if (state == 3) {
            if (chr == 93) {
                state = 4;
            }
        }
    }
    if (state == 4) {
        return 1;
    }
    return 0;
}
