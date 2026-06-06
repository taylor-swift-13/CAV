/*
Input to this function is a string represented multiple groups for nested parentheses separated by spaces.
For each of the group, output the deepest level of nesting of parentheses.
E.g. (()()) has maximum two levels of nesting while ((())) has three.

>>> p006_parse_nested_parens("(()()) ((())) () ((())()())")
{2, 3, 1, 3}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_6_pre: list Z -> Prop)
               (problem_6_spec: list Z -> list Z -> Prop)
               (ascii_range: list Z -> Prop)
               (paren_prefix_output: Z -> list Z -> list Z)
               (paren_prefix_in_group: Z -> list Z -> Z)
               (paren_prefix_level: Z -> list Z -> Z)
               (paren_prefix_max: Z -> list Z -> Z)
               (paren_final_output: list Z -> Z -> Z -> list Z)
               (paren_step_output: list Z -> Z -> Z -> Z -> list Z)
               (paren_step_in_group: Z -> Z -> Z)
               (paren_step_level: Z -> Z -> Z -> Z)
               (paren_step_max: Z -> Z -> Z -> Z) */
/*@ Import Coq Require Import p006_parse_nested_parens */

typedef struct {
    int *data;
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

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

IntArray *p006_parse_nested_parens(char *paren_string)
/*@ With l len orig
    Require
        paren_string == orig &&
        0 <= len && len + 1 < INT_MAX &&
        Zlength(l) == len &&
        problem_6_pre(l) &&
        ascii_range(l) &&
        CharArray::full(paren_string, len + 1, app(l, cons(0, nil)))
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        output_size == Zlength(output_l) &&
        0 <= output_size && output_size <= len &&
        problem_6_spec(l, output_l) &&
        CharArray::full(orig, len + 1, app(l, cons(0, nil))) *
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, len)
*/
{
    IntArray *out = malloc_int_array_struct();
    int n = strlen(paren_string);
    out->size = 0;
    out->data = malloc_int_array(n);
    int *data = out->data;
    int level = 0;
    int max_level = 0;
    int in_group = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (paren_string[i] == 32) {
            if (in_group) {
                data[out->size] = max_level;
                out->size = out->size + 1;
                level = 0;
                max_level = 0;
                in_group = 0;
            }
        } else {
            in_group = 1;
            if (paren_string[i] == 40) {
                level = level + 1;
                if (level > max_level) {
                    max_level = level;
                }
            } else {
                if (level > 0) {
                    level = level - 1;
                }
            }
        }

    }

    if (in_group) {
        data[out->size] = max_level;
        out->size = out->size + 1;
    }

    return out;
}
