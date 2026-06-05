#include "../verification_stdlib.h"

int ex_queen_attack_bool(int r1, int c1, int r2, int c2)
/*@ Require
      0 <= r1 && r1 <= 2147483647 &&
      0 <= c1 && c1 <= 2147483647 &&
      0 <= r2 && r2 <= 2147483647 &&
      0 <= c2 && c2 <= 2147483647 &&
      emp
    Ensure
      (__return == 1 =>
        (r1@pre == r2@pre ||
         c1@pre == c2@pre ||
         r1@pre - r2@pre == c1@pre - c2@pre ||
         r1@pre - r2@pre == c2@pre - c1@pre)) &&
      (__return == 0 =>
        r1@pre != r2@pre &&
        c1@pre != c2@pre &&
        r1@pre - r2@pre != c1@pre - c2@pre &&
        r1@pre - r2@pre != c2@pre - c1@pre) &&
      emp
*/
{
    int dr = r1 - r2;
    int dc = c1 - c2;

    if (dr < 0) {
        dr = -dr;
    }
    if (dc < 0) {
        dc = -dc;
    }
    return r1 == r2 || c1 == c2 || dr == dc;
}
