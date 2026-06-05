#include "../verification_stdlib.h"

int ex_raindrops_code(int n)
/*@ Require
      n > 0 &&
      emp
    Ensure
      0 <= __return &&
      __return <= 7 &&
      (n@pre % 3 == 0 && n@pre % 5 != 0 && n@pre % 7 != 0 => __return == 1) &&
      (n@pre % 3 != 0 && n@pre % 5 == 0 && n@pre % 7 != 0 => __return == 2) &&
      (n@pre % 3 == 0 && n@pre % 5 == 0 && n@pre % 7 != 0 => __return == 3) &&
      (n@pre % 3 != 0 && n@pre % 5 != 0 && n@pre % 7 == 0 => __return == 4) &&
      (n@pre % 3 == 0 && n@pre % 5 != 0 && n@pre % 7 == 0 => __return == 5) &&
      (n@pre % 3 != 0 && n@pre % 5 == 0 && n@pre % 7 == 0 => __return == 6) &&
      (n@pre % 3 == 0 && n@pre % 5 == 0 && n@pre % 7 == 0 => __return == 7) &&
      (n@pre % 3 != 0 && n@pre % 5 != 0 && n@pre % 7 != 0 => __return == 0) &&
      emp
*/
{
    int code = 0;
    if (n % 3 == 0) code |= 1;
    if (n % 5 == 0) code |= 2;
    if (n % 7 == 0) code |= 4;
    return code;
}
