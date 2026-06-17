/*
Given a string, find out how many distinct characters (regardless of case) does it consist of
>>> p016_count_distinct_characters("xyzXYZ")
3
>>> p016_count_distinct_characters("Jerry")
4
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_16_pre: list Z -> Prop)
               (problem_16_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (lower: Z -> Z)
               (lower_seen_state: Z -> Z -> list Z -> Z -> Z -> Prop)
               (count_distinct_lower_upto: Z -> list Z -> Z) */
/*@ Import Coq Require Import string_bridge */
/*@ Import Coq Require Import p016_count_distinct_characters */

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

int p016_count_distinct_characters(char *str)
/*@ With l len
    Require 0 <= len && len < INT_MAX &&
            Zlength(l) == len &&
            problem_16_pre(l) &&
            ascii_range(l) &&
            (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
            CharArray::full(str, len + 1, app(l, cons(0, nil)))
    Ensure problem_16_spec(l, __return) &&
           (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
           CharArray::full(str, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(str) /*@ where l = l, n = len */;
    int count = 0;
    int i;

    /*@ Inv Assert
          str == str@pre &&
          n == len &&
          problem_16_pre(l) &&
          ascii_range(l) &&
          Zlength(l) == len &&
          0 <= n && n < INT_MAX &&
          0 <= i && i <= n &&
          0 <= count && count <= i &&
          count == count_distinct_lower_upto(i, l) &&
          (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
          CharArray::full(str, len + 1, app(l, cons(0, nil)))
    */
    for (i = 0; i < n; i++) {
        int c = str[i];
        int seen = 0;
        int j;

        if (c >= 65 && c <= 90) {
            c = c + 32;
        }

        /*@ Inv Assert
              str == str@pre &&
              n == len &&
              problem_16_pre(l) &&
              ascii_range(l) &&
              Zlength(l) == len &&
              0 <= n && n < INT_MAX &&
              0 <= i && i < n &&
              0 <= count && count <= i &&
              count == count_distinct_lower_upto(i, l) &&
              c == lower(Znth(i, l, 0)) &&
              0 <= j && j <= i &&
              lower_seen_state(j, i, l, c, seen) &&
              (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
              CharArray::full(str, len + 1, app(l, cons(0, nil)))
        */
        for (j = 0; j < i; j++) {
            int d = str[j];
            if (d >= 65 && d <= 90) {
                d = d + 32;
            }
            if (d == c) {
                seen = 1;
            }
        }

        if (seen == 0) {
            count = count + 1;
        }
    }
    return count;
}
