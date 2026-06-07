/*
Create a function that returns true if the last character
of a given string is an alphabetical character && is !
a part of a word, && false otherwise.
Note: "word" is a group of characters separated by space.

Examples:
p134_check_if_last_char_is_a_letter("apple pie") -> false
p134_check_if_last_char_is_a_letter("apple pi e") -> true
p134_check_if_last_char_is_a_letter("apple pi e ") -> false
p134_check_if_last_char_is_a_letter("") -> false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_134_pre: list Z -> Prop)
               (problem_134_spec: list Z -> Z -> Prop)
               (is_alpha: Z -> Prop)
               (ascii_range: list Z -> Prop) */
/*@ Import Coq Require Import p134_check_if_last_char_is_a_letter */

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

int p134_check_if_last_char_is_a_letter(char *txt)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        ascii_range(l) &&
        problem_134_pre(l) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        CharArray::full(txt, len + 1, app(l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        problem_134_spec(l, __return) &&
        CharArray::full(txt, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(txt);
    if (n == 0) return 0;

    int chr = txt[n - 1];
    if (chr < 65) return 0;
    if (chr > 90 && chr < 97) return 0;
    if (chr > 122) return 0;

    if (n == 1) return 1;

    chr = txt[n - 2];
    if (chr == 32) return 1;
    return 0;
}
