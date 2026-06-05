#include "verification_stdlib.h"

int apple_purchase_total(int count, int price)
/*@ Require
      count >= 0 &&
      price >= 0 &&
      count * price <= 2147483647 &&
      emp
    Ensure
      __return == count@pre * price@pre && emp
*/
{
    return count * price;
}
