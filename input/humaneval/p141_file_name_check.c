/*
Create a function which takes a string representing a file's name, && returns
"Yes" if the the file's name is valid, && returns "No" otherwise.
A file's name is considered to be valid if && only if all the following conditions
are met:
- There should ! be more than three digits ('0'-'9') in the file's name.
- The file's name contains exactly one dot "."
- The substring before the dot should ! be empty, && it starts with a letter from
the latin alphapet ('a'-'z' && 'A'-'Z').
- The substring after the dot should be one of these: {'txt", "exe", "dll"}
Examples:
p141_file_name_check("example.txt") => "Yes"
p141_file_name_check("1example.dll")  => "No" // (the name should start with a latin alphapet letter)
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Import Coq Require Import string_bridge */
/*@ Extern Coq (problem_141_pre: list Z -> Prop)
               (problem_141_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (is_digit: Z -> Prop)
               (is_alpha: Z -> Prop)
               (suffix_ok: list Z -> Prop)
               (digit_count_upto: Z -> list Z -> Z)
               (dot_count_upto: Z -> list Z -> Z)
               (file_name_checks: list Z -> Prop) */
/*@ Import Coq Require Import p141_file_name_check */

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

int p141_file_name_check(char *file_name)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_141_pre(l) &&
        ascii_range(l) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        CharArray::full(file_name, len + 1, app(l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        problem_141_spec(l, __return) &&
        CharArray::full(file_name, len + 1, app(l, cons(0, nil)))
*/
{
    int numdigit = 0;
    int numdot = 0;
    int i = 0;
    int alpha = 0;
    int suffix = 0;
    int n = strlen(file_name) /*@ where l = l, n = len */;

    if (n < 5) {
        return 0;
    }

    int w = file_name[0];
    if (w >= 65) {
        if (w <= 90) {
            alpha = 1;
        } else {
            if (w >= 97) {
                if (w <= 122) {
                    alpha = 1;
                }
            }
        }
    }
    if (alpha == 0) {
        return 0;
    }

    int c0 = file_name[n - 4];
    int c1 = file_name[n - 3];
    int c2 = file_name[n - 2];
    int c3 = file_name[n - 1];
    if (c0 == 46) {
        if (c1 == 116) {
            if (c2 == 120) {
                if (c3 == 116) {
                    suffix = 1;
                }
            }
        }
        if (c1 == 101) {
            if (c2 == 120) {
                if (c3 == 101) {
                    suffix = 1;
                }
            }
        }
        if (c1 == 100) {
            if (c2 == 108) {
                if (c3 == 108) {
                    suffix = 1;
                }
            }
        }
    }
    if (suffix == 0) {
        return 0;
    }

    while (i < n) {
        if (file_name[i] >= 48 && file_name[i] <= 57) {
            numdigit += 1;
        }
        if (file_name[i] == 46) {
            numdot += 1;
        }
        i += 1;
    }

    if (numdigit > 3) {
        return 0;
    }
    if (numdot != 1) {
        return 0;
    }

    return 1;
}
