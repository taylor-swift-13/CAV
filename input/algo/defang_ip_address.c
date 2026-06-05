#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (defang_ip_address_spec : list Z -> list Z) */
/*@ Import Coq Require Import defang_ip_address */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure exists l, CharArray::full(__return, n, l)
*/
;

char *defang_ip_address(char *address)
/*@ With l len
    Require
      address != 0 &&
      0 <= len &&
      3 * len + 1 <= 2147483647 &&
      Zlength(l) == len &&
      (forall (k: Z), (0 <= k && k < len) => l[k] != 0) &&
      CharArray::full(address, len + 1, app(l, cons(0, nil)))
    Ensure
      CharArray::full(address, len + 1, app(l, cons(0, nil))) *
      CharArray::full(__return, Zlength(defang_ip_address_spec(l)) + 1,
        app(defang_ip_address_spec(l), cons(0, nil)))
*/
{
    int n = 0;
    int dots = 0;

    while (1) {
        if (address[n] == 0) {
            break;
        }
        if (address[n] == 46) {
            dots++;
        }
        n++;
    }

    int total = n + dots * 2 + 1;
    char *out = malloc_char_array(total);
    int i = 0;
    int pos = 0;

    while (i < n) {
        if (address[i] == 46) {
            out[pos] = 91;
            pos++;
            out[pos] = 46;
            pos++;
            out[pos] = 93;
            pos++;
        } else {
            out[pos] = address[i];
            pos++;
        }
        i++;
    }

    out[pos] = 0;
    return out;
}
