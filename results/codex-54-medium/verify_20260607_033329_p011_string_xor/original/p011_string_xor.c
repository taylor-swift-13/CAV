#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure exists l, CharArray::full(__return, n, l)
*/
;

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

char *p011_string_xor(char *a, char *b)
/*@ With l1 l2 na nb
    Require 0 <= na && na < INT_MAX &&
        0 <= nb && nb < INT_MAX &&
        Zlength(l1) == na &&
        Zlength(l2) == nb &&
        (forall (k: Z), (0 <= k && k < na) => Znth(k, l1, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < nb) => Znth(k, l2, 0) != 0) &&
        CharArray::full(a, na + 1, app(l1, cons(0, nil))) *
        CharArray::full(b, nb + 1, app(l2, cons(0, nil)))
    Ensure exists out_l n,
        (forall (k: Z), (0 <= k && k < na) => Znth(k, l1, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < nb) => Znth(k, l2, 0) != 0) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, out_l, 0) != 0) &&
        ((na <= nb && n == na) || (nb < na && n == nb)) &&
        CharArray::full(a, na + 1, app(l1, cons(0, nil))) *
        CharArray::full(b, nb + 1, app(l2, cons(0, nil))) *
                CharArray::full(__return, n + 1, app(out_l, cons(0, nil))) &&
                (forall (k: Z), (0 <= k && k < n) =>
                    ((Znth(k, l1, 0) == Znth(k, l2, 0) && Znth(k, out_l, 0) == 48) ||
                     (Znth(k, l1, 0) != Znth(k, l2, 0) && Znth(k, out_l, 0) == 49)))
*/
{
    int i;
    int n1 = strlen(a);
    int n2 = strlen(b);
    int n;
    if (n1 < n2) {
        n = n1;
    } else {
        n = n2;
    }


    char *output = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        if (a[i] == b[i]) {
            output[i] = 48;
        } else {
            output[i] = 49;
        }
    }
    output[n] = 0;
    return output;
}
