#include "../verification_stdlib.h"

int arithmetic_series(int a, int d, int n)
/*@ Require
      n >= 0 &&
      -2147483648 <= n * a + d * n * (n - 1) / 2 &&
      n * a + d * n * (n - 1) / 2 <= 2147483647 &&
      emp
    Ensure
      __return == n@pre * a@pre + d@pre * n@pre * (n@pre - 1) / 2 && emp
*/
{
    int i = 0;
    int cur = a;
    int sum = 0;
    while (i < n) {
        sum += cur;
        cur += d;
        i++;
    }
    return sum;
}
