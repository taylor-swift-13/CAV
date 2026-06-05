/*
decode_cyclic_38 takes as input a string encoded with encode_cyclic and returns
the decoded string. Only decode_cyclic_38 is verified for problem 38.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_38_pre_z: list Z -> Prop)
               (problem_38_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (full_decode_len_z: Z -> Z)
               (decode_char_z: Z -> list Z -> Z -> Z)
               (decode_source_index_z: Z -> Z -> Z) */
/*@ Import Coq Require Import coins_38 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

char *decode_cyclic_38(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_38_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        exists out_l,
        Zlength(out_l) == len &&
        problem_38_spec_z(l, out_l) &&
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
