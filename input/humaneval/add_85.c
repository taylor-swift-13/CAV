/*
Given a non-empty vector of integers lst. add_85 the even elements that are at odd indices.

Examples:
    add_85({4, 2, 6, 7}) ==> 2
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_85_pre: list Z -> Prop)
               (problem_85_spec: list Z -> Z -> Prop)
               (sum_even_at_odd_upto: Z -> list Z -> Z)
               (add_int_range: list Z -> Prop) */
/*@ Import Coq Require Import add_85 */

int add_85(int *lst, int lst_size)
/*@ With lv
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        lst_size == Zlength(lv) &&
        problem_85_pre(lv) &&
        add_int_range(lv) &&
        IntArray::full(lst, lst_size, lv)
    Ensure
        problem_85_spec(lv, __return) &&
        IntArray::full(lst, lst_size, lv)
*/
{
    int s = 0;
    int i;

    for (i = 0; i * 2 + 1 < lst_size; i++)
        if (lst[i * 2 + 1] % 2 == 0) s += lst[i * 2 + 1];
    return s;
}
