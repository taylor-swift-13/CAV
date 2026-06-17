/*
You are given 2 words. You need to return true if the second word or any of its rotations is a substring in the first word
p154_cycpattern_check("abcd","abd") => false
p154_cycpattern_check("hello","ell") => true
p154_cycpattern_check("whassup","psus") => false
p154_cycpattern_check("abab","baa") => true
p154_cycpattern_check("efef","eeff") => false
p154_cycpattern_check("himenss","simen") => true

*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_154_pre: list Z -> list Z -> Prop)
               (problem_154_spec: list Z -> list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (rot_index: Z -> Z -> Z -> Z)
               (rotation_match_progress: Z -> Z -> Z -> Z -> list Z -> list Z -> Prop)
               (rotation_match_at_spec: Z -> Z -> list Z -> list Z -> Prop)
               (rotation_shift_search: Z -> Z -> Z -> list Z -> list Z -> Prop)
               (rotation_shift_has_match: Z -> list Z -> list Z -> Prop)
               (rotation_any_search: Z -> Z -> list Z -> list Z -> Prop)
               (rotation_any_match: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import p154_cycpattern_check */

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

int rotation_match_at(char *a, char *b, int pos, int shift, int n, int m)
/*@ With a_l b_l
    Require
        0 <= n && n < INT_MAX &&
        0 < m && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        ascii_range(a_l) &&
        ascii_range(b_l) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, a_l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < m) => Znth(k, b_l, 0) != 0) &&
        0 <= pos && pos + m <= n &&
        0 <= shift && shift < m &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < n) => Znth(k, a_l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < m) => Znth(k, b_l, 0) != 0) &&
        ((__return == 1 && rotation_match_at_spec(pos, shift, a_l, b_l)) ||
         (__return == 0 && !(rotation_match_at_spec(pos, shift, a_l, b_l)))) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
*/
{
    int ok = 1;
    int j;

    for (j = 0; j < m; j++) {
        int idx = shift + j;
        if (idx >= m) {
            idx = idx - m;
        }
        if (a[pos + j] != b[idx]) {
            ok = 0;
        }
    }
    return ok;
}

int rotation_occurs_at_shift(char *a, char *b, int shift, int n, int m)
/*@ With a_l b_l
    Require
        0 <= n && n < INT_MAX &&
        0 < m && m <= n && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        ascii_range(a_l) &&
        ascii_range(b_l) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, a_l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < m) => Znth(k, b_l, 0) != 0) &&
        0 <= shift && shift < m &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < n) => Znth(k, a_l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < m) => Znth(k, b_l, 0) != 0) &&
        ((__return == 1 && rotation_shift_has_match(shift, a_l, b_l)) ||
         (__return == 0 && !(rotation_shift_has_match(shift, a_l, b_l)))) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
*/
{
    int found = 0;
    int pos;

    for (pos = 0; pos <= n - m; pos++) {
        int ok = rotation_match_at(a, b, pos, shift, n, m) /*@ where a_l = a_l, b_l = b_l */;
        if (ok == 1) {
            found = 1;
        }
    }
    return found;
}

int p154_cycpattern_check(char *a, char *b)
/*@ With a_l n b_l m
    Require
        0 <= n && n < INT_MAX &&
        0 <= m && m < INT_MAX / 2 &&
        Zlength(a_l) == n &&
        Zlength(b_l) == m &&
        problem_154_pre(a_l, b_l) &&
        ascii_range(a_l) &&
        ascii_range(b_l) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, a_l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < m) => Znth(k, b_l, 0) != 0) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < n) => Znth(k, a_l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < m) => Znth(k, b_l, 0) != 0) &&
        problem_154_spec(a_l, b_l, __return) &&
        CharArray::full(a, n + 1, app(a_l, cons(0, nil))) *
        CharArray::full(b, m + 1, app(b_l, cons(0, nil)))
*/
{
    int n0 = strlen(a) /*@ where l = a_l, n = n */;
    int m0 = strlen(b) /*@ where l = b_l, n = m */;

    if (m0 == 0) {
        return 1;
    }
    if (m0 > n0) {
        return 0;
    }

    int found = 0;
    int shift;

    for (shift = 0; shift < m0; shift++) {
        int ok = rotation_occurs_at_shift(a, b, shift, n0, m0) /*@ where a_l = a_l, b_l = b_l */;
        if (ok == 1) {
            found = 1;
        }
    }
    return found;
}
