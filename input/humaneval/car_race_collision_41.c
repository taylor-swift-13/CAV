#include "verification_stdlib.h"

int car_race_collision_41(int n)
/*@ Require
        INT_MIN <= n && n <= INT_MAX && emp
    Ensure
        __return == n * n && emp
*/
{
    return n*n;
}