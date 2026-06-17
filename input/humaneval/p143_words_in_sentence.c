/*
You are given a string representing a sentence,
the sentence contains some words separated by a space,
and you have to return a string that contains the words from the original sentence,
whose lengths are prime numbers,
the order of the words in the new string should be the same as the original one.

Example 1:
    Input: sentence = "This is a test"
    Output: "is"

Example 2:
    Input: sentence = "lets go for swimming"
    Output: "go for"

Constraints:
    * 1 <= len(sentence) <= 100
    * sentence contains only letters
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_143_pre: list Z -> Prop)
               (problem_143_spec: list Z -> list Z -> Prop)
               (ascii_range: list Z -> Prop)
               (words_in_sentence_prefix: Z -> list Z -> list Z)
	               (words_in_sentence_output: list Z -> list Z)
	               (prime_len_flag: Z -> Z)
	               (append_selected_word: list Z -> list Z -> Z -> Z -> list Z)
	               (word_chars: list Z -> Z -> Z -> Prop)
	               (word_start: list Z -> Z -> Prop)
	               (scan_ready: list Z -> Z -> Z -> Prop)
	               (word_copy_prefix: Z -> Z -> list Z -> list Z)
	               (prime_loop_state: Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p143_words_in_sentence */

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

int is_prime_len(int len)
/*@ Require 0 <= len && len <= 100 && emp
    Ensure __return == prime_len_flag(len)
*/
{
    int j;
    int composite = 0;
    if (len < 2) {
        return 0;
    }

    for (j = 2; j < len; j++) {
        if (len % j == 0) {
            composite = 1;
        }
    }

    if (composite == 1) {
        return 0;
    }
    return 1;
}

char *p143_words_in_sentence(char *sentence)
/*@ With l len
    Require
        1 <= len && len <= 100 &&
        Zlength(l) == len &&
        problem_143_pre(l) &&
        ascii_range(l) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        CharArray::full(sentence, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l out_len,
        0 <= out_len && out_len <= len + 1 &&
        Zlength(out_l) == out_len &&
        out_l == words_in_sentence_output(l) &&
        problem_143_spec(l, out_l) &&
        CharArray::full(sentence, len + 1, app(l, cons(0, nil))) *
        CharArray::full(__return, out_len + 1, app(out_l, cons(0, nil))) *
        CharArray::undef_seg(__return, out_len + 1, len + 2)
*/
{
    int n = strlen(sentence) /*@ where l = l, n = len */;
    char *out = malloc_char_array(n + 2);
    int out_len = 0;
    int i = 0;

    while (i < n) {
        while (i < n && sentence[i] == 32) {
            i = i + 1;
        }

        if (i < n) {
            int start = i;

            while (i < n && sentence[i] != 32) {
                i = i + 1;
            }

            int word_len = i - start;
            int prime = is_prime_len(word_len);
            if (prime == 1) {
                int k;
                if (out_len > 0) {
                    out[out_len] = 32;
                    out_len = out_len + 1;
                }

                for (k = 0; k < word_len; k++) {
                    out[out_len] = sentence[start + k];
                    out_len = out_len + 1;
                }
            }
        }
    }

    out[out_len] = 0;
    return out;
}
