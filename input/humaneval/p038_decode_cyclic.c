/*
p038_decode_cyclic takes as input a string encoded with encode_cyclic and returns
the decoded string. Only p038_decode_cyclic is verified for problem 38.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Import Coq Require Import string_bridge */
/*@ Extern Coq (problem_38_pre: list Z -> Prop)
               (problem_38_spec: list Z -> list Z -> Prop)
               (ascii_range: list Z -> Prop)
               (full_decode_len: Z -> Z)
               (decode_char: Z -> list Z -> Z -> Z)
               (decode_source_index: Z -> Z -> Z) */
/*@ Import Coq Require Import p038_decode_cyclic */

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

char *p038_decode_cyclic(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_38_pre(l) &&
        ascii_range(l) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        exists out_l,
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, out_l, 0) != 0) &&
        Zlength(out_l) == len &&
        problem_38_spec(l, out_l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil))) *
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    int n = strlen(s) /*@ where l = l, n = len */;
    char *out = malloc_char_array(n + 1);
    int full = (n / 3) * 3;
    int i;

    for (i = 0; i < n; i++) {
        if (i < full) {
            if ((i + 1) % 3 == 1) {
                out[i] = s[i + 2];
            } else {
                out[i] = s[i - 1];
            }
        } else {
            out[i] = s[i];
        }
    }
    out[n] = 0;
    return out;
}
