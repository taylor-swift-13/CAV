/*
In this problem, you will implement a function that takes two vectors of numbers,
&& determines whether it is possible to perform an p110_exchange of elements
between them to make lst1 a vector of only even numbers.
There is no limit on the number of exchanged elements between lst1 && lst2.
If it is possible to p110_exchange elements between the lst1 && lst2 to make
all the elements of lst1 to be even, return "YES".
Otherwise, return "NO".
For example:
p110_exchange({1, 2, 3, 4}, {1, 2, 3, 4}) => "YES"
p110_exchange({1, 2, 3, 4}, {1, 5, 3, 4}) => "NO"
It is assumed that the input vectors will be non-empty.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_110_pre: list Z -> list Z -> Prop)
               (problem_110_spec: list Z -> list Z -> Z -> Prop)
               (nonnegative_list: list Z -> Prop)
               (count_even_upto: Z -> list Z -> Z)
               (count_even_list: list Z -> Z) */
/*@ Import Coq Require Import p110_exchange */

int p110_exchange(int* lst1, int lst1_size, int* lst2, int lst2_size)
/*@ With l1 l2
    Require
        0 < lst1_size && lst1_size < INT_MAX &&
        0 < lst2_size && lst2_size < INT_MAX &&
        lst1_size + lst2_size < INT_MAX &&
        Zlength(l1) == lst1_size &&
        Zlength(l2) == lst2_size &&
        problem_110_pre(l1, l2) &&
        nonnegative_list(l1) &&
        nonnegative_list(l2) &&
        IntArray::full(lst1, lst1_size, l1) *
        IntArray::full(lst2, lst2_size, l2)
    Ensure
        problem_110_spec(l1, l2, __return) &&
        IntArray::full(lst1, lst1_size, l1) *
        IntArray::full(lst2, lst2_size, l2)
*/
{
    int num = 0;

    for (int i = 0; i < lst1_size; i++) {
        if (lst1[i] % 2 == 0) {
            num += 1;
        }
    }


    for (int i = 0; i < lst2_size; i++) {
        if (lst2[i] % 2 == 0) {
            num += 1;
        }
    }

    if (num >= lst1_size) return 1;
    return 0;
}
