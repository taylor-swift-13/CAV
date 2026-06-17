/*
Given a positive integer n, return a vector that has the number of even && odd
integer palindromes that fall within the range(1, n), inclusive.

Example 1:

    Input: 3
    Output: (1, 2)
    Explanation:
    Integer palindrome are 1, 2, 3. one of them is even, && two of them are odd.

Example 2:

    Input: 12
    Output: (4, 6)
    Explanation:
    Integer palindrome are 1, 2, 3, 4, 5, 6, 7, 8, 9, 11. four of them are even, && 6 of them are odd.

Note:
    1. 1 <= n <= 10^3
    2. returned vector has the number of even && odd integer palindromes respectively.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_107_pre: Z -> Prop)
               (problem_107_spec: Z -> list Z -> Prop)
               (pal_reverse_loop_state: Z -> Z -> Z -> Prop)
               (is_pal_model: Z -> Z)
               (pal_count_prefix: Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p107_even_odd_palindrome */

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

static int is_pal(int x)
/*@ With (x0: Z)
    Require
        x == x0 &&
        1 <= x0 && x0 <= 1000 && emp
    Ensure
        __return == is_pal_model(x0) && emp
*/
{
    int r = 0;
    int t = x;
    while (t > 0) {
        r = r * 10 + (t % 10);
        t /= 10;
    }
    return r == x;
}

IntArray *p107_even_odd_palindrome(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        1 <= n0 && n0 <= 1000 &&
        problem_107_pre(n0)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == 2 &&
        output_l == cons(Znth(0, output_l, 0), cons(Znth(1, output_l, 0), nil)) &&
        problem_107_spec(n0, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, output_size, output_l)
*/
{
    int num1=0,num2=0;
    IntArray *out = malloc_int_array_struct();
    int i;
    for (i=1;i<=n;i++)
    {
        if (is_pal(i) && i%2==1) num1+=1;
        if (is_pal(i) && i%2==0) num2+=1;
    }
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    data[0] = num2;
    data[1] = num1;
    return out;
}
