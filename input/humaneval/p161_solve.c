/*
Given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Import Coq Require Import string_bridge */
/*@ Extern Coq (problem_161_pre: list Z -> Prop)
               (problem_161_spec: list Z -> list Z -> Prop)
               (ascii_range: list Z -> Prop)
               (contains_letter_prefix: Z -> list Z -> Z)
               (contains_letter: list Z -> Z)
               (flip_char: Z -> Z) */
/*@ Import Coq Require Import p161_solve */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

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

char *p161_solve(char *s)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            problem_161_pre(l) &&
            ascii_range(l) &&
            (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
            CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l,
            (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
            (forall (k: Z), (0 <= k && k < len) => Znth(k, out_l, 0) != 0) &&
            Zlength(out_l) == len &&
            problem_161_spec(l, out_l) &&
            CharArray::full(s, len + 1, app(l, cons(0, nil))) *
            CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int i;
    int n = strlen(s) /*@ where l = l, n = len */;
    int has_letter = 0;
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = s[i];
        if ((w >= 65 && w <= 90) || (w >= 97 && w <= 122)) {
            has_letter = 1;
        }
    }

    if (has_letter == 1) {
        for (i = 0; i < n; i++) {
            int w = s[i];
            if (w >= 65 && w <= 90) {
                w = w + 32;
            } else if (w >= 97 && w <= 122) {
                w = w - 32;
            }
            out[i] = w;
        }
    } else {
        for (i = 0; i < n; i++) {
            out[i] = s[n - 1 - i];
        }
    }
    out[n] = 0;
    return out;
}
