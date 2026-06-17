/*
Circular shift the digits of the integer x, shift the digits right by shift
&& return the result as a string.
If shift > number of digits, return digits reversed.
>>> p065_circular_shift(12, 1)
"21"
>>> p065_circular_shift(12, 2)
"12"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_65_pre: Z -> Z -> Prop)
               (problem_65_spec: Z -> Z -> list Z -> Prop)
               (decimal_digits: Z -> list Z)
               (circular_shift_output: Z -> Z -> list Z)
               (circular_shift_prefix: Z -> Z -> Z -> list Z -> Prop)
               (base_digits: Z -> Z -> list Z)
               (base_count_state: Z -> Z -> Z -> Z -> Prop)
               (base_fill_full_state: Z -> Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import base_conversion_lib */
/*@ Import Coq Require Import p065_circular_shift */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* p065_circular_shift(int x, int shift)
/*@ Require
        0 <= x && x <= INT_MAX &&
        0 <= shift && shift <= INT_MAX &&
        problem_65_pre(x, shift) &&
        Zlength(decimal_digits(x)) + 1 < 64
    Ensure exists out_l len scratch,
        (forall (k: Z), (0 <= k && k < len) => Znth(k, out_l, 0) != 0) &&
        len == Zlength(out_l) &&
        len == Zlength(circular_shift_output(x, shift)) &&
        problem_65_spec(x, shift, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil))) *
        CharArray::full(scratch,
            Zlength(decimal_digits(x)) + 1,
            app(decimal_digits(x), cons(0, nil))) *
        CharArray::undef_seg(scratch, Zlength(decimal_digits(x)) + 1, 64)
*/
{
    char *buf = malloc_char_array(64);
    int n = 0;
    int tmp = 0;
    int i = 0;
    int fill = 0;

    if (x == 0) {
        buf[0] = 48;
        buf[1] = 0;
        n = 1;
        } else {
        tmp = x;
        while (tmp > 0) {
            n = n + 1;
            tmp = tmp / 10;
        }

        for (i = 0; i <= n; i++) {
            buf[i] = 0;
        }

        tmp = x;
        fill = n;

        while (tmp > 0) {
            fill = fill - 1;
            buf[fill] = 48 + (tmp % 10);
            tmp = tmp / 10;
        }

        }

    char *out = malloc_char_array(n + 1);

    if (n < shift) {
        for (i = 0; i < n; i++) {
            out[i] = buf[n - 1 - i];
        }
    } else {
        for (i = 0; i < n; i++) {
            int src = n - shift + i;
            if (src >= n) {
                src = src - n;
            }
            out[i] = buf[src];
        }
    }

    out[n] = 0;
    return out;
}
