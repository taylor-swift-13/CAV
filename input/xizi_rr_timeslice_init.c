#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void xizi_rr_timeslice_init(int *state)
/*@ With l
    Require
      Zlength(l) == 2 &&
      IntArray::full(state, 2, l)
    Ensure
      exists l0,
        Zlength(l0) == 2 &&
        l0[0] == 10 &&
        l0[1] == 10 &&
        IntArray::full(state, 2, l0)
*/
{
    state[0] = 10;
    state[1] = 10;
}
