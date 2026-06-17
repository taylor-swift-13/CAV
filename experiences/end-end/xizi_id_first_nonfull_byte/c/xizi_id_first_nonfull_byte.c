#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

int xizi_id_first_nonfull_byte(int n, int *id_map)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(id_map, n, l)
    Ensure
      ((__return == -1 &&
        (forall (i: Z), (0 <= i && i < n) => ((l[i] & 255) == 255))) ||
       (0 <= __return && __return < n &&
        ((l[__return] & 255) != 255) &&
        (forall (i: Z), (0 <= i && i < __return) => ((l[i] & 255) == 255)))) &&
      IntArray::full(id_map, n, l)
*/
{
    int i;

    for (i = 0; i < n; ++i) {
        if ((id_map[i] & 255) != 255) {
            return i;
        }
    }

    return -1;
}
