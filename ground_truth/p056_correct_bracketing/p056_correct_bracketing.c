/*
brackets is a string of '<' && '>'.
return true if every opening bracket has a corresponding closing bracket.

>>> p056_correct_bracketing("<")
false
>>> p056_correct_bracketing("<>")
true
>>> p056_correct_bracketing("<<><>>")
true
>>> p056_correct_bracketing("><<>")
false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_56_pre: list Z -> Prop)
               (problem_56_spec: list Z -> Z -> Prop)
               (angle_level_upto: Z -> list Z -> Z)
               (angle_nonnegative_prefix: Z -> list Z -> Prop)
               (ascii_range: list Z -> Prop) */
/*@ Import Coq Require Import string_bridge */
/*@ Import Coq Require Import p056_correct_bracketing */

int strlen(char *s)
/*@ With l n
    Require 0 <= n && n < INT_MAX &&
            Zlength(l) == n &&
            (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
            CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int p056_correct_bracketing(char *brackets)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        ascii_range(l) &&
        problem_56_pre(l) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        CharArray::full(brackets, len + 1, app(l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        problem_56_spec(l, __return) &&
        CharArray::full(brackets, len + 1, app(l, cons(0, nil)))
*/
{
    int level = 0;
    int n = strlen(brackets) /*@ where l = l, n = len */;
    int i;
    /*@ Inv Assert
        brackets == brackets@pre &&
        n == len &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        ascii_range(l) &&
        problem_56_pre(l) &&
        0 <= i && i <= n &&
        0 <= level && level <= i &&
        level == angle_level_upto(i, l) &&
        angle_nonnegative_prefix(i, l) &&
        CharArray::full(brackets, n + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        if (brackets[i] == 60) {
            level = level + 1;
        } else if (brackets[i] == 62) {
            level = level - 1;
        }
        if (level < 0) {
            return 0;
        }
    }
    if (level != 0) {
        return 0;
    }
    return 1;
}
