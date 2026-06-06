/*
Change numerical base of input number x to base.
return string representation after the conversion.
base numbers are less than 10.
>>> change_base_44(8, 3)
"22"
>>> change_base_44(8, 2)
"1000"
>>> change_base_44(7, 2)
"111"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_44_pre: Z -> Z -> Prop)
               (problem_44_spec: Z -> Z -> list Z -> Prop)
               (base_digits: Z -> Z -> list Z)
               (base_digits_pos: Z -> Z -> list Z)
               (base_count_state: Z -> Z -> Z -> Z -> Prop)
               (base_fill_state: Z -> Z -> Z -> Z -> list Z -> Prop)
               (base_fill_full_state: Z -> Z -> Z -> Z -> list Z -> Prop)
               (repeat_Z: {A} -> A -> Z -> list A) */
/*@ Import Coq Require Import change_base_44 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* change_base_44(int x, int base)
/*@ Require
        0 <= x && x < INT_MAX &&
        2 <= base && base < 10 &&
        problem_44_pre(x, base)
    Ensure exists out_l len,
        1 <= len && len < INT_MAX &&
        Zlength(out_l) == len &&
        problem_44_spec(x, base, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil)))
*/
{
    if (x == 0) {
        char *out0 = malloc_char_array(2);
        out0[0] = 48;
        out0[1] = 0;
        return out0;
    } else {
        int digits = 0;
        int t = x;
        int total = 0;
        char *out = 0;
        int i = 0;

        while (t > 0) {
            digits = digits + 1;
            t = t / base;
        }

        total = digits;
        out = malloc_char_array(total + 1);

        for (i = 0; i <= total; i++) {
            out[i] = 0;
        }

        
        while (x > 0) {
            digits = digits - 1;
            
            out[digits] = 48 + (x % base);
            x = x / base;
        }
        return out;
    }
}
