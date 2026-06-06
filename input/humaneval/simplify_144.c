/*
Your task is to implement a function that will simplify_144 the expression
x * n. The function returns true if x * n evaluates to a whole number && false
otherwise. Both x && n, are string representation of a fraction, && have the following format,
<numerator>/<denominator> where both numerator && denominator are positive whole numbers.

You can assume that x, && n are valid fractions, && do ! have zero as denominator.

simplify_144("1/5", "5/1") = true
simplify_144("1/6", "2/1") = false
simplify_144("7/10", "10/2") = false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_144_pre: list Z -> list Z -> Prop)
               (problem_144_spec: list Z -> list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (fraction_parts: list Z -> Z -> Z -> Z -> Prop)
               (fraction_values_safe: Z -> Z -> Z -> Z -> Prop)
               (parse_digits: list Z -> Z) */
/*@ Import Coq Require Import simplify_144 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int simplify_144(char *x, char *n)
/*@ With lx ln lenx lenn sx sn ax bx cn dn
    Require
        0 <= lenx && lenx < INT_MAX &&
        0 <= lenn && lenn < INT_MAX &&
        Zlength(lx) == lenx &&
        Zlength(ln) == lenn &&
        problem_144_pre(lx, ln) &&
        ascii_range(lx) &&
        ascii_range(ln) &&
        fraction_parts(lx, sx, ax, bx) &&
        fraction_parts(ln, sn, cn, dn) &&
        fraction_values_safe(ax, bx, cn, dn) &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
    Ensure
        problem_144_spec(lx, ln, __return) &&
        CharArray::full(x, lenx + 1, app(lx, cons(0, nil))) *
        CharArray::full(n, lenn + 1, app(ln, cons(0, nil)))
*/
{
    int a = 0;
    int b = 0;
    int c = 0;
    int d = 0;
    int i;

    int x_len = strlen(x);

    for (i = 0; x[i] != 47; i++) {
        a = a * 10 + (x[i] - 48);
    }

    i = i + 1;

    for (; i < x_len; i++) {
        b = b * 10 + (x[i] - 48);
    }

    int n_len = strlen(n);

    
    for (i = 0; n[i] != 47; i++) {
        c = c * 10 + (n[i] - 48);
    }

    i = i + 1;

    for (; i < n_len; i++) {
        d = d * 10 + (n[i] - 48);
    }

    int product_num = a * c;
    int product_den = b * d;
    if (product_num % product_den == 0) return 1;
    return 0;
}
