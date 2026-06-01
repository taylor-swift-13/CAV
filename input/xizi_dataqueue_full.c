#include "../../verification_stdlib.h"

int xizi_dataqueue_full(int front, int rear, int max_len)
/*@ Require
      1 < max_len &&
      0 <= front &&
      front < max_len &&
      0 <= rear &&
      rear < max_len &&
      emp
    Ensure
      ((__return == 1 &&
        (rear@pre + 1) % max_len@pre == front@pre) ||
       (__return == 0 &&
        (rear@pre + 1) % max_len@pre != front@pre)) &&
      emp
*/
{
    if ((rear + 1) % max_len == front) {
        return 1;
    }

    return 0;
}
