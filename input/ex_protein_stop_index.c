#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (ex_protein_stop_index_spec : list Z -> Z) */
/*@ Import Coq Require Import ex_protein_stop_index */

int ex_protein_stop_index(const char *rna)
/*@ With l n
    Require
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      n % 3 == 0 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(rna, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == ex_protein_stop_index_spec(l) &&
      CharArray::full(rna, n + 1, app(l, cons(0, nil)))
*/
{
    int idx = 0;
    int i = 0;

    while (1) {
        if (rna[i] == 0) {
            break;
        }
        if (rna[i] == 85 &&
            ((rna[i + 1] == 65 && (rna[i + 2] == 65 || rna[i + 2] == 71)) ||
             (rna[i + 1] == 71 && rna[i + 2] == 65))) {
            return idx;
        }
        i += 3;
        idx++;
    }

    return idx;
}
