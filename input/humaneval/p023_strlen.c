/*
Return length of given string
>>> p023_strlen("")
0
>>> p023_strlen("abc")
3
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_23_pre: list Z -> Prop)
               (problem_23_spec: list Z -> Z -> Prop) */
/*@ Import Coq Require Import p023_strlen */

int p023_strlen(char *str)
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
    int i = 0;

    while (1) {
        if (str[i] == 0) {
            break;
        }
        i++;
    }

    return i;
}
