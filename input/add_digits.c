#include "../verification_stdlib.h"

int add_digits(int num)
/*@ Require
      0 <= num &&
      emp
    Ensure
      (num@pre == 0 => __return == 0) &&
      (num@pre > 0 && num@pre % 9 == 0 => __return == 9) &&
      (num@pre > 0 && num@pre % 9 != 0 => __return == num@pre % 9) &&
      0 <= __return &&
      __return <= 9 &&
      emp
*/
{
    while (num >= 10) {
        int sum = 0;
        while (num > 0) { sum += num % 10; num /= 10; }
        num = sum;
    }
    return num;
}
