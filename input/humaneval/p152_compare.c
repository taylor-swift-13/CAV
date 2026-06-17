/*
Your task is to determine if a person correctly guessed the results of a number of matches.
You are given two arrays of scores and guesses of equal length, where each index shows a match.
Return an array of the same length denoting how far off each guess was. If they have guessed correctly,
the value is 0, and if not, the value is the absolute difference between the guess and the score.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs: Z -> Z)
               (problem_152_pre: list Z -> list Z -> Prop)
               (problem_152_spec: list Z -> list Z -> list Z -> Prop)
               (compare_prefix: Z -> list Z -> list Z -> list Z -> Prop)
               (compare_int_range: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import p152_compare */

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) {
        return -x;
    }
    else {
        return x;
    }
}

IntArray *p152_compare(int* game, int game_size, int* guess, int guess_size)
/*@ With game_l guess_l
    Require
        0 <= game_size && game_size < INT_MAX &&
        0 <= guess_size && guess_size < INT_MAX &&
        game_size == Zlength(game_l) &&
        guess_size == Zlength(guess_l) &&
        game_size == guess_size &&
        problem_152_pre(game_l, guess_l) &&
        compare_int_range(game_l, guess_l) &&
        IntArray::full(game, game_size, game_l) *
        IntArray::full(guess, guess_size, guess_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == game_size &&
        output_size == Zlength(output_l) &&
        problem_152_spec(game_l, guess_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(game, game_size, game_l) *
        IntArray::full(guess, guess_size, guess_l) *
        IntArray::full(data, output_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    int n;
    if (game_size < guess_size) {
        n = game_size;
    } else {
        n = guess_size;
    }
    out->size = n;
    out->data = malloc_int_array(n);
    int *data = out->data;
    if (data == 0) {
        out->size = 0;
        return out;
    }
    int i;

    for (i=0;i<n;i++) {
        int diff;
        int value;
        diff = game[i] - guess[i];
        value = abs(diff);
        data[i] = value;

    }
    return out;
}
