/*
Given a positive integer, obtain its roman numeral equivalent as a string,
and return it in lowercase.
Restrictions: 1 <= num <= 1000

Examples:
>>> int_to_mini_roman(19) == "xix"
>>> int_to_mini_roman(152) == "clii"
>>> int_to_mini_roman(426) == "cdxxvi"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_156_pre: Z -> Prop)
               (problem_156_spec: Z -> list Z -> Prop)
               (roman_digit: Z -> Z -> Z -> Z -> list Z -> Prop)
               (roman_thousand_list: Z -> list Z)
               (roman_thousand: Z -> list Z -> Prop)
               (roman_prefix1_list: Z -> list Z)
               (roman_prefix1: Z -> list Z -> Prop)
               (roman_prefix2_list: Z -> list Z)
               (roman_prefix2: Z -> list Z -> Prop)
               (roman_output_list: Z -> list Z)
               (roman_output: Z -> list Z -> Prop) */
/*@ Import Coq Require Import int_to_mini_romank_156 */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int append_roman_digit(char *out, int pos, int one, int ten, int five, int digit)
/*@ With prefix cap
    Require
        0 <= pos && pos + 4 < cap && cap <= INT_MAX &&
        0 <= digit && digit <= 9 &&
        0 <= one && one <= 127 &&
        0 <= ten && ten <= 127 &&
        0 <= five && five <= 127 &&
        Zlength(prefix) == pos &&
        CharArray::full(out, pos, prefix) *
        CharArray::undef_seg(out, pos, cap)
    Ensure exists chunk,
        roman_digit(one, ten, five, digit, chunk) &&
        pos <= __return && __return < cap &&
        __return == pos + Zlength(chunk) &&
        CharArray::full(out, __return, app(prefix, chunk)) *
        CharArray::undef_seg(out, __return, cap)
*/
{
    if (digit == 0) {
        return pos;
    } else if (digit == 1) {
        out[pos] = one;
        return pos + 1;
    } else if (digit == 2) {
        out[pos] = one;
        out[pos + 1] = one;
        return pos + 2;
    } else if (digit == 3) {
        out[pos] = one;
        out[pos + 1] = one;
        out[pos + 2] = one;
        return pos + 3;
    } else if (digit == 4) {
        out[pos] = one;
        out[pos + 1] = five;
        return pos + 2;
    } else if (digit == 5) {
        out[pos] = five;
        return pos + 1;
    } else if (digit == 6) {
        out[pos] = five;
        out[pos + 1] = one;
        return pos + 2;
    } else if (digit == 7) {
        out[pos] = five;
        out[pos + 1] = one;
        out[pos + 2] = one;
        return pos + 3;
    } else if (digit == 8) {
        out[pos] = five;
        out[pos + 1] = one;
        out[pos + 2] = one;
        out[pos + 3] = one;
        return pos + 4;
    } else {
        out[pos] = one;
        out[pos + 1] = ten;
        return pos + 2;
    }
}

int append_roman_thousand(char *out, int number)
/*@ With cap
    Require
        1 <= number && number <= 1000 &&
        1 < cap && cap <= INT_MAX &&
        CharArray::undef_full(out, cap)
    Ensure exists prefix,
        roman_thousand(number, prefix) &&
        0 <= __return && __return < cap &&
        __return == Zlength(prefix) &&
        CharArray::full(out, __return, prefix) *
        CharArray::undef_seg(out, __return, cap)
*/
{
    if (number == 1000) {
        out[0] = 109;
        return 1;
    } else {
        return 0;
    }
}

char* int_to_mini_romank_156(int number)
/*@ Require
        1 <= number && number <= 1000 &&
        problem_156_pre(number)
    Ensure exists out_l len,
        0 <= len && len < 64 &&
        Zlength(out_l) == len &&
        problem_156_spec(number, out_l) &&
        CharArray::full(__return, len + 1, app(out_l, cons(0, nil))) *
        CharArray::undef_seg(__return, len + 1, 64)
*/
{
    int original = number;
    int k = 0;
    int h = 0;
    int t = 0;
    int o = 0;
    char *out = malloc_char_array(64);

    k = append_roman_thousand(out, number) /*@ where cap = 64 */;

    h = (number / 100) % 10;
    k = append_roman_digit(out, k, 99, 109, 100, h)
        /*@ where prefix = roman_thousand_list(number), cap = 64 */;

    t = (number / 10) % 10;
    k = append_roman_digit(out, k, 120, 99, 108, t)
        /*@ where prefix = roman_prefix1_list(number), cap = 64 */;

    o = number % 10;
    k = append_roman_digit(out, k, 105, 120, 118, o)
        /*@ where prefix = roman_prefix2_list(number), cap = 64 */;

    out[k] = 0;
    return out;
}
