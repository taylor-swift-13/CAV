#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (xizi_single_link_wf : Z -> list Z -> Prop) */
/*@ Extern Coq (xizi_single_link_len_spec : Z -> list Z -> Z) */
/*@ Import Coq Require Import xizi_single_link_len */

int xizi_single_link_len(int head, int *next)
/*@ With n l
    Require
      0 <= n &&
      n <= 2147483647 &&
      Zlength(l) == n &&
      0 <= head &&
      head < n &&
      xizi_single_link_wf(head, l) &&
      IntArray::full(next, n, l)
    Ensure
      __return == xizi_single_link_len_spec(head@pre, l) &&
      IntArray::full(next, n, l)
*/
{
    int length = 0;
    int node = next[head];

    while (node != -1) {
        node = next[node];
        length++;
    }

    return length;
}
