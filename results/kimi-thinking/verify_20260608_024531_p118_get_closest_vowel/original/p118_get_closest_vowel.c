/*
You are given a word. Your task is to find the closest vowel that stands between
two consonants from the right side of the word (case sensitive).

Vowels in the beginning && ending doesn't count. Return empty string if you didn't
find any vowel met the above condition.

You may assume that the given string contains English letter only.

Example:
p118_get_closest_vowel("yogurt") ==> "u"
p118_get_closest_vowel("FULL") ==> "U"
p118_get_closest_vowel("quick") ==> ""
p118_get_closest_vowel("ab") ==> ""
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_118_pre: list Z -> Prop)
               (problem_118_spec: list Z -> list Z -> Prop)
               (is_vowel: Z -> Prop)
               (is_consonant: Z -> Prop)
               (alpha_range: list Z -> Prop)
               (ascii_range: list Z -> Prop)
               (closest_vowel_candidate: list Z -> Z -> Prop)
               (no_candidate_after: Z -> list Z -> Prop) */
/*@ Import Coq Require Import p118_get_closest_vowel */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 &&
           CharArray::full(__return, 0, nil) *
           CharArray::undef_seg(__return, 0, n)
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

int is_vowel_code(int ch)
/*@ Require emp
    Ensure ((__return == 1 && is_vowel(ch@pre)) ||
            (__return == 0 && ! is_vowel(ch@pre))) &&
           emp
*/
{
    if (ch == 65) return 1;
    if (ch == 69) return 1;
    if (ch == 73) return 1;
    if (ch == 79) return 1;
    if (ch == 85) return 1;
    if (ch == 97) return 1;
    if (ch == 101) return 1;
    if (ch == 105) return 1;
    if (ch == 111) return 1;
    if (ch == 117) return 1;
    return 0;
}

char *p118_get_closest_vowel(char *word)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_118_pre(l) &&
        ascii_range(l) &&
        alpha_range(l) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        CharArray::full(word, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l out_n,
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < out_n) => Znth(k, out_l, 0) != 0) &&
        Zlength(out_l) == out_n &&
        0 <= out_n && out_n <= 1 &&
        problem_118_spec(l, out_l) &&
        CharArray::full(word, len + 1, app(l, cons(0, nil))) *
        CharArray::full(__return, out_n + 1, app(out_l, cons(0, nil)))
*/
{
    int i;
    int cur;
    int right;
    int left;
    int cur_vowel;
    int right_vowel;
    int left_vowel;
    int n = strlen(word);
    cur = 0;
    right = 0;
    left = 0;
    cur_vowel = 0;
    right_vowel = 0;
    left_vowel = 0;

    if (n < 3) {
        char *out = malloc_char_array(1);
        out[0] = 0;
        return out;
    }

    i = n - 2;

    while (i >= 1) {
        cur = word[i];
        right = word[i + 1];
        left = word[i - 1];
        cur_vowel = is_vowel_code(cur);
        if (cur_vowel == 1) {
            right_vowel = is_vowel_code(right);
            if (right_vowel == 0) {
                left_vowel = is_vowel_code(left);
                if (left_vowel == 0) {

                    char *out = malloc_char_array(2);
                    out[0] = cur;
                    out[1] = 0;
                    return out;
                }
            }
        }

        i -= 1;
    }

    char *out = malloc_char_array(1);
    out[0] = 0;
    return out;
}
