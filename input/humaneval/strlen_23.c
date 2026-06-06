/*
Return length of given string
>>> strlen_23("")
0
>>> strlen_23("abc")
3
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_23_pre: list Z -> Prop)
               (problem_23_spec: list Z -> Z -> Prop) */
/*@ Import Coq Require Import strlen_23 */

int strlen_23(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int string_length(char *str)
/*@ With l n
    Require
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_23_pre(l) &&
        CharArray::full(str, n + 1, app(l, cons(0, nil)))
    Ensure
        __return == n &&
        problem_23_spec(l, __return) &&
        CharArray::full(str, n + 1, app(l, cons(0, nil)))
*/
{
    int ret = strlen_23(str);
    return ret;
}
