/*
Find the shortest palindrome that begins with a supplied string.
Algorithm idea is simple:
- Find the longest postfix of supplied string that is a palindrome.
- Append to the end of the string reverse of a string prefix that comes before the palindromic suffix.
>>> p010_make_palindrome("")
""
>>> p010_make_palindrome("cat")
"catac"
>>> p010_make_palindrome("cata")
"catac"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Import Coq Require Import string_bridge */
/*@ Extern Coq (problem_10_pre: list Z -> Prop)
               (problem_10_spec: list Z -> list Z -> Prop)
               (ascii_range: list Z -> Prop)
               (pal_suffix: Z -> list Z -> Prop)
               (first_pal_suffix: Z -> list Z -> Prop)
               (make_pal_output: Z -> list Z -> list Z) */
/*@ Import Coq Require Import p010_make_palindrome */

int strlen(char *s)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
            CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure __return == len &&
           (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
           CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
;

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int is_pal_suffix(char *s, int start, int n)
/*@ With l
    Require
        0 <= start && start <= n &&
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        ascii_range(l) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
        ((__return == 1 && pal_suffix(start, l)) ||
         (__return == 0 && !(pal_suffix(start, l)))) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int i = start;
    int j = n - 1;

    if (start == n) {
        return 1;
    }

    while (i < j) {
        if (s[i] != s[j]) {
            return 0;
        }
        i = i + 1;
        j = j - 1;
    }
    return 1;
}

char *p010_make_palindrome(char *str)
/*@ With l len
    Require
        0 <= len && len < INT_MAX / 2 &&
        Zlength(l) == len &&
        problem_10_pre(l) &&
        ascii_range(l) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l,
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < Zlength(out_l)) => Znth(k, out_l, 0) != 0) &&
        problem_10_spec(l, out_l) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil))) *
        CharArray::full(__return, Zlength(out_l) + 1, app(out_l, cons(0, nil)))
*/
{
    int n = strlen(str) /*@ where l = l, len = len */;
    int best = n;
    int i;

    for (i = 0; i < n; i++) {
        if (best == n) {
            int ok = is_pal_suffix(str, i, n) /*@ where l = l */;
            if (ok == 1) {
                best = i;
            }
        }
    }

    if (best == n) {
        best = 0;
    }

    int out_len = n + best;
    char *out = malloc_char_array(out_len + 1);

    for (i = 0; i < n; i++) {
        out[i] = str[i];
    }

    int k;
    for (k = 0; k < best; k++) {
        out[n + k] = str[best - 1 - k];
    }

    out[out_len] = 0;
    return out;
}
