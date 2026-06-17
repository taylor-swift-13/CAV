/*
Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> p015_string_sequence(0)
"0"
>>> p015_string_sequence(5)
"0 1 2 3 4 5"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_15_pre: Z -> Prop)
               (problem_15_spec: Z -> list Z -> Prop)
               (sequence_prefix: Z -> list Z)
               (sequence_output: Z -> list Z)
               (sequence_output_bound: Z -> Prop)
               (base_digits: Z -> Z -> list Z)
               (base_count_state: Z -> Z -> Z -> Z -> Prop)
               (base_fill_full_state: Z -> Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import p015_string_sequence */
/*@ Import Coq Require Import p015_string_sequence */
/*@ Import Coq Require Import base_conversion_lib */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* p015_string_sequence(int n)
/*@ Require
        0 <= n &&
        12 * (n + 1) + 1 < INT_MAX &&
        problem_15_pre(n) &&
        sequence_output_bound(n)
    Ensure exists out_l len cap,
        (forall (k: Z), (0 <= k && k < len) => Znth(k, out_l, 0) != 0) &&
        cap == 12 * (n + 1) + 1 &&
        len == Zlength(out_l) &&
        problem_15_spec(n, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil))) *
        CharArray::undef_seg(__return, len + 1, cap)
*/
{
    int cap = 12 * (n + 1) + 1;
    char *out = malloc_char_array(cap);
    int k = 0;
    int i = 1;

    out[0] = 48;
    k = 1;

    {
    int t = 0;
    int digits = 0;
    int j = 0;
    int fill = 0;

    for (i = 1; i <= n; i++) {
        t = i;
        digits = 0;

        while (t > 0) {
            digits = digits + 1;
            t = t / 10;
        }

        out[k] = 32;
        k = k + 1;

        for (j = 0; j < digits; j++) {
            out[k + j] = 0;
        }

        t = i;
        fill = digits;

        while (t > 0) {
            fill = fill - 1;

            out[k + fill] = 48 + (t % 10);
            t = t / 10;
        }

        k = k + digits;
    }
    }

    out[k] = 0;

    return out;
}
