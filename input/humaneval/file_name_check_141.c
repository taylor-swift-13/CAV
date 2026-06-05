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
file_name_check_141("example.txt") => "Yes"
file_name_check_141("1example.dll")  => "No" // (the name should start with a latin alphapet letter)
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_141_pre_z: list Z -> Prop)
               (problem_141_spec_z: list Z -> Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (is_digit_z: Z -> Prop)
               (is_alpha_z: Z -> Prop)
               (suffix_ok_z: list Z -> Prop)
               (digit_count_upto: Z -> list Z -> Z)
               (dot_count_upto: Z -> list Z -> Z)
               (file_name_checks_z: list Z -> Prop) */
/*@ Import Coq Require Import coins_141 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int file_name_check_141(char *file_name)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_141_pre_z(l) &&
        ascii_range_z(l) &&
        CharArray::full(file_name, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_141_spec_z(l, __return) &&
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
