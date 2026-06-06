#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

int p003_below_zero(int *operations, int operations_size)
/*@ With l
    Require 0 <= operations_size && operations_size < INT_MAX &&
        (forall (k: Z), (0 <= k && k < operations_size) =>
            (INT_MIN <= sum(sublist(0, k + 1, l)) &&
             sum(sublist(0, k + 1, l)) <= INT_MAX)) &&
        IntArray::full(operations, operations_size, l)
    Ensure ((__return != 0) &&
        (exists k, 0 <= k && k < operations_size &&
               sum(sublist(0, k + 1, l)) < 0) ||
        (__return == 0) &&
        (forall (k: Z), (0 <= k && k < operations_size) =>
               0 <= sum(sublist(0, k + 1, l)))) &&
       IntArray::full(operations, operations_size, l)
*/
{
    int num = 0;
    int i;

    for (i = 0; i < operations_size; i++) {
        num += operations[i];
        if (num < 0) {
            return 1;
        }
    }
    return 0;
}
