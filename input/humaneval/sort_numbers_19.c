/*
Input is a space-delimited string of numberals from "zero" to "nine".
Valid choices are "zero", "one", "two", "three", "four", "five", "six",
"seven", "eight" and "nine".
Return the string with numbers sorted from smallest to largest.
>>> sort_numbers_19("three one five")
"one three five"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
#include "int_array_def.h"
#include "ptr_array_def.h"

/*@ Extern Coq (problem_19_pre_z: list Z -> Prop)
               (problem_19_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (number_word_z: Z -> list Z)
               (number_word_len_z: Z -> Z)
               (token_prefix_z: Z -> Z -> list Z -> list Z)
               (token_unsat_end_z: Z -> Z -> list Z -> Prop)
               (token_empty_start_z: Z -> Z -> list Z -> Prop)
               (scan_counts_z: Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (output_prefix_z: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z)
               (output_capacity_prefix_z: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z)
               (output_prefix_by_input_z: Z -> Z -> list Z -> list Z)
               (output_capacity_prefix_by_input_z: Z -> list Z -> Z)
               (sorted_numbers_output_by_counts_z: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z)
               (number_words_full: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
               (number_words_missing: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion) */
/*@ Import Coq Require Import coins_19 */
/*@ include strategies "number_words_19.strategies" */

int strlen(char *s)
/*@ With l len
    Require
        0 <= len &&
        Zlength(l) == len &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        __return == len &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
;

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

void free_char_array(char *p, int used, int cap)
/*@ With l
    Require
        p != 0 &&
        0 <= used && used <= cap &&
        Zlength(l) == used &&
        CharArray::full(p, used, l) *
        CharArray::undef_seg(p, used, cap)
    Ensure emp
*/
;

int strcmp(char *a, char *b)
/*@ With la lb lena lenb
    Require
        0 <= lena && 0 <= lenb &&
        Zlength(la) == lena &&
        Zlength(lb) == lenb &&
        CharArray::full(a, lena + 1, app(la, cons(0, nil))) *
        CharArray::full(b, lenb + 1, app(lb, cons(0, nil)))
    Ensure
        ((__return == 0 && la == lb) || (__return != 0 && la != lb)) &&
        CharArray::full(a, lena + 1, app(la, cons(0, nil))) *
        CharArray::full(b, lenb + 1, app(lb, cons(0, nil)))
*/
;

void strcat(char *dst, char *src)
/*@ With dst_l src_l dst_len src_len cap
    Require
        0 <= dst_len && 0 <= src_len &&
        dst_len + src_len + 1 <= cap &&
        Zlength(dst_l) == dst_len &&
        Zlength(src_l) == src_len &&
        CharArray::full(dst, dst_len + 1, app(dst_l, cons(0, nil))) *
        CharArray::undef_seg(dst, dst_len + 1, cap) *
        CharArray::full(src, src_len + 1, app(src_l, cons(0, nil)))
    Ensure
        CharArray::full(dst,
                        dst_len + src_len + 1,
                        app(app(dst_l, src_l), cons(0, nil))) *
        CharArray::undef_seg(dst, dst_len + src_len + 1, cap) *
        CharArray::full(src, src_len + 1, app(src_l, cons(0, nil)))
*/
;

char* sort_numbers_19(char *numbers)
/*@ With l len
    Require
        0 <= len && len + 1 < INT_MAX &&
        Zlength(l) == len &&
        problem_19_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(numbers, len + 1, app(l, cons(0, nil)))
    Ensure exists out_l,
        problem_19_spec_z(l, out_l) &&
        CharArray::full(__return, Zlength(out_l) + 1, app(out_l, cons(0, nil))) *
        CharArray::full(numbers, len + 1, app(l, cons(0, nil)))
*/
{
    char w0[5];
    char w1[4];
    char w2[4];
    char w3[6];
    char w4[5];
    char w5[5];
    char w6[4];
    char w7[6];
    char w8[6];
    char w9[5];
    char *words[10];
    char *space_word;
    int count[10];
    int n = strlen(numbers) /*@ where l = l, len = len */;
    char *token;
    int tlen = 0;
    int out_len = 1;
    char *out;
    int i;
    int d;
    int j;
    int first;
    int cmp;
    char ch;
    char *word;

    w0[0] = 122; w0[1] = 101; w0[2] = 114; w0[3] = 111; w0[4] = 0;
    w1[0] = 111; w1[1] = 110; w1[2] = 101; w1[3] = 0;
    w2[0] = 116; w2[1] = 119; w2[2] = 111; w2[3] = 0;
    w3[0] = 116; w3[1] = 104; w3[2] = 114; w3[3] = 101; w3[4] = 101; w3[5] = 0;
    w4[0] = 102; w4[1] = 111; w4[2] = 117; w4[3] = 114; w4[4] = 0;
    w5[0] = 102; w5[1] = 105; w5[2] = 118; w5[3] = 101; w5[4] = 0;
    w6[0] = 115; w6[1] = 105; w6[2] = 120; w6[3] = 0;
    w7[0] = 115; w7[1] = 101; w7[2] = 118; w7[3] = 101; w7[4] = 110; w7[5] = 0;
    w8[0] = 101; w8[1] = 105; w8[2] = 103; w8[3] = 104; w8[4] = 116; w8[5] = 0;
    w9[0] = 110; w9[1] = 105; w9[2] = 110; w9[3] = 101; w9[4] = 0;
    words[0] = w0; words[1] = w1; words[2] = w2; words[3] = w3; words[4] = w4;
    words[5] = w5; words[6] = w6; words[7] = w7; words[8] = w8; words[9] = w9;
    space_word = malloc_char_array(3);
    space_word[0] = 32; space_word[1] = 0;
    ch = 0;
    d = 0;
    j = 0;
    first = 0;
    cmp = 0;
    word = 0;
    out = 0;
    token = malloc_char_array(32);

    for (i = 0; i < 10; i++) {
        count[i] = 0;
    }

    for (i = 0; i <= n; i++) {
        if (i < n) {
            ch = numbers[i];
        } else {
            ch = 32;
        }
        if (ch == 32) {
            if (tlen > 0) {
                token[tlen] = 0;
                
                for (d = 0; d < 10; d++) {
                    word = words[d];
                    cmp = strcmp(token, word)
                        /*@ where la = token_prefix_z(i, tlen, l),
                                  lb = number_word_z(d),
                                  lena = tlen,
                                  lenb = number_word_len_z(d) */;
                    if (cmp == 0) {
                        count[d] = count[d] + 1;
                        break;
                    }
                }
                tlen = 0;
            }
        } else if (tlen < 31) {
            token[tlen] = ch;
            tlen = tlen + 1;
        }
    }

    free_char_array(token, tlen, 32)
        /*@ where l = token_prefix_z(i, tlen, l) */;

    for (i = 0; i < 10; i++) {
        word = words[i];
        out_len = out_len + count[i] *
            (strlen(word) /*@ where l = number_word_z(i),
                                     len = number_word_len_z(i) */ + 1);
    }

    out = malloc_char_array(out_len);
    out[0] = 0;
    first = 1;

    for (i = 0; i < 10; i++) {
        word = words[i];
        
        for (j = 0; j < count[i]; j++) {
            if (first == 0) {
                strcat(out, space_word)
                    /*@ where dst_l = output_prefix_by_input_z(i, j, l),
                              src_l = number_word_z(10),
                              dst_len = Zlength(output_prefix_by_input_z(i, j, l)),
                              src_len = number_word_len_z(10),
                              cap = out_len */;
                strcat(out, word)
                    /*@ where dst_l = app(output_prefix_by_input_z(i, j, l),
                                          number_word_z(10)),
                              src_l = number_word_z(i),
                              dst_len = Zlength(output_prefix_by_input_z(i, j, l)) +
                                        number_word_len_z(10),
                              src_len = number_word_len_z(i),
                              cap = out_len */;
            } else {
                strcat(out, word)
                    /*@ where dst_l = output_prefix_by_input_z(i, j, l),
                              src_l = number_word_z(i),
                              dst_len = Zlength(output_prefix_by_input_z(i, j, l)),
                              src_len = number_word_len_z(i),
                              cap = out_len */;
            }
            first = 0;
        }
    }
    free_char_array(space_word, 2, 3)
        /*@ where l = app(number_word_z(10), cons(0, nil)) */;
    
    return out;
}
