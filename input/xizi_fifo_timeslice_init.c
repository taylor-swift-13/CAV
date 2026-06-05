#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void xizi_fifo_timeslice_init(int *state)
/*@ With l
    Require
      Zlength(l) == 2 &&
      IntArray::full(state, 2, l)
    Ensure
      exists l0,
        Zlength(l0) == 2 &&
        l0[0] == 0 &&
        l0[1] == 0 &&
        IntArray::full(state, 2, l0)
*/
{
    state[0] = 0;
    state[1] = 0;
}

