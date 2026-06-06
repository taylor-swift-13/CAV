/*
You'll be given a string of words, && your task is to count the number
of boredoms. A boredom is a sentence that starts with the word "I".
Sentences are delimited by '.', '?' || '!'.

For example:
>>> is_bored_91("Hello world")
0
>>> is_bored_91("The sky is blue. The sun is shining. I love this weather")
1
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_91_pre: list Z -> Prop)
               (problem_91_spec: list Z -> Z -> Prop)
               (bored_sum_prefix: Z -> list Z -> Z)
               (bored_isstart_prefix: Z -> list Z -> Z)
               (bored_isi_prefix: Z -> list Z -> Z)
               (ascii_range: list Z -> Prop) */
/*@ Import Coq Require Import is_bored_91 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int is_bored_91(char *S)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        ascii_range(l) &&
        problem_91_pre(l) &&
        CharArray::full(S, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_91_spec(l, __return) &&
        CharArray::full(S, len + 1, app(l, cons(0, nil)))
*/
{
    int i;
    int isstart = 1;
    int isi = 0;
    int sum = 0;
    int n = strlen(S);

    for (i = 0; i < n; i++) {
        int chr = S[i];
        if (chr == 32 && isi == 1) {
            isi = 0;
            sum += 1;
        }
        if (chr == 73 && isstart == 1) {
            isi = 1;
        } else {
            isi = 0;
        }
        if (chr != 32) {
            isstart = 0;
        }
        if (chr == 46 || chr == 63 || chr == 33) {
            isstart = 1;
        }
    }
    return sum;
}
