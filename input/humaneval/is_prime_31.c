#include "verification_stdlib.h"

int is_prime_31(long long n)
/*@ Require
        INT_MIN <= n && n <= INT_MAX && emp
    Ensure
        (__return == 1=> (n >= 2 && (forall k, 2 <= k && k < n => n % k != 0))) &&
        (__return == 0 => (n < 2 || (exists k, 2 <= k && k < n && n % k == 0))) && 
        emp
*/
{
    if (n < 2) return 0;
    long long i;
    
    for (i = 2; i * i <= n; i++) {
        if (n % i == 0) return 0;
    }
    return 1;
}