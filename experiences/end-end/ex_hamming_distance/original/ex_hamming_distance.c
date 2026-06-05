#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (ex_hamming_distance_pre : list Z -> list Z -> Prop) */
/*@ Extern Coq (ex_hamming_distance_spec : list Z -> list Z -> Z) */
/*@ Import Coq Require Import ex_hamming_distance */

int ex_hamming_distance(const char *a, const char *b)
/*@ With la lb na nb
    Require
      a != 0 && b != 0 &&
      0 <= na && na < 2147483647 &&
      0 <= nb && nb < 2147483647 &&
      Zlength(la) == na &&
      Zlength(lb) == nb &&
      ex_hamming_distance_pre(la, lb) &&
      (forall (k: Z), (0 <= k && k < na) => la[k] != 0) &&
      (forall (k: Z), (0 <= k && k < nb) => lb[k] != 0) &&
      CharArray::full((char *)a, na + 1, app(la, cons(0, nil))) *
      CharArray::full((char *)b, nb + 1, app(lb, cons(0, nil)))
    Ensure
      __return == ex_hamming_distance_spec(la, lb) &&
      CharArray::full((char *)a, na + 1, app(la, cons(0, nil))) *
      CharArray::full((char *)b, nb + 1, app(lb, cons(0, nil)))
*/
{
    int d = 0;
    int i = 0;

    while (1) {
        if (a[i] == 0) {
            break;
        }
        if (a[i] != b[i]) {
            d++;
        }
        i++;
    }

    return d;
}
