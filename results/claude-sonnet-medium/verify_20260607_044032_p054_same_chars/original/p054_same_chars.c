/*
Check if two words have the same characters.
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddeddabc")
true
>>> p054_same_chars("abcd", "dddddddabc")
true
>>> p054_same_chars("dddddddabc", "abcd")
true
>>> p054_same_chars("eabcd", "dddddddabc")
false
>>> p054_same_chars("abcd", "dddddddabce")
false
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddddabc")
false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_54_pre: list Z -> list Z -> Prop)
               (problem_54_spec: list Z -> list Z -> Z -> Prop)
               (no_zero: list Z -> Prop)
               (ascii_range: list Z -> Prop)
               (char_in: Z -> list Z -> Prop)
               (same_chars_prefix: Z -> list Z -> list Z -> Prop)
               (same_chars_all: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import p054_same_chars */

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

char *strchr(char *s, int c)
/*@ With l n
    Require 0 <= n && n < INT_MAX &&
            Zlength(l) == n &&
            (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
            CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure ((__return == 0 && ! char_in(c, l)) ||
            (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
            (__return != 0 && char_in(c, l))) &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int p054_same_chars(char *s0, char *s1)
/*@ With l0 n0 l1 n1
    Require 0 <= n0 && n0 < INT_MAX &&
            0 <= n1 && n1 < INT_MAX &&
            Zlength(l0) == n0 &&
            Zlength(l1) == n1 &&
            problem_54_pre(l0, l1) &&
            ascii_range(l0) &&
            ascii_range(l1) &&
            no_zero(l0) &&
            no_zero(l1) &&
            CharArray::full(s0, n0 + 1, app(l0, cons(0, nil))) *
            CharArray::full(s1, n1 + 1, app(l1, cons(0, nil)))
    Ensure problem_54_spec(l0, l1, __return) &&
           (forall (k: Z), (0 <= k && k < n0) => Znth(k, l0, 0) != 0) &&
           (forall (k: Z), (0 <= k && k < n1) => Znth(k, l1, 0) != 0) &&
           CharArray::full(s0, n0 + 1, app(l0, cons(0, nil))) *
           CharArray::full(s1, n1 + 1, app(l1, cons(0, nil)))
*/
{
    int len0 = strlen(s0);
    int len1 = strlen(s1);
    int i;

    for (i = 0; i < len0; i++)
    {
        int chr = s0[i];
        char *found = strchr(s1, chr);
        if (found == 0) {
            return 0;
        }
    }

    for (i = 0; i < len1; i++)
    {
        int chr = s1[i];
        char *found = strchr(s0, chr);
        if (found == 0) {
            return 0;
        }
    }
    return 1;
}
