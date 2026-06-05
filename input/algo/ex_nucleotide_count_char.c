#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (string_count_char_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import string_count_char */

int ex_nucleotide_count_char(const char *dna, const char *target)
/*@ With l n t
    Require
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      (t == 65 || t == 67 || t == 71 || t == 84) &&
      (forall (k: Z),
        (0 <= k && k < n) =>
          (l[k] == 65 || l[k] == 67 || l[k] == 71 || l[k] == 84)) &&
      CharArray::full(dna, n + 1, app(l, cons(0, nil))) *
      CharArray::full(target, 2, cons(t, cons(0, nil)))
    Ensure
      __return == string_count_char_spec(l, t) &&
      CharArray::full(dna, n + 1, app(l, cons(0, nil))) *
      CharArray::full(target, 2, cons(t, cons(0, nil)))
*/
{
    int ans = 0;
    int i = 0;

    while (1) {
        if (dna[i] == 0) {
            break;
        }
        if (dna[i] == target[0]) {
            ans++;
        }
        i++;
    }

    return ans;
}
