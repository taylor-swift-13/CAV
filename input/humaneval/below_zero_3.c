#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (below_zero_prefix_safe: list Z -> Prop)
               (problem_3_spec: list Z -> Z -> Prop) */
/*@ Import Coq Require Import below_zero_3 */

int below_zero_3(int *operations, int operations_size)
/*@ With l
    Require 0 <= operations_size && operations_size < INT_MAX &&
        operations_size == Zlength(l) &&
        below_zero_prefix_safe(l) &&
        IntArray::full(operations, operations_size, l)
    Ensure problem_3_spec(l, __return) &&
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
