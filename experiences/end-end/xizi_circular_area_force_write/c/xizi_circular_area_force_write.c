#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void xizi_circular_area_force_write(int *state, int data_length, int area_length, int force)
/*@ With l
    Require
      state != 0 &&
      0 < area_length &&
      area_length <= 1073741824 &&
      Zlength(l) == 3 &&
      IntArray::full(state, 3, l) &&
      0 <= l[0] &&
      l[0] < area_length &&
      0 <= l[1] &&
      l[1] < area_length &&
      0 <= data_length &&
      data_length <= area_length
    Ensure
      exists lr,
        Zlength(lr) == 3 &&
        IntArray::full(state, 3, lr) &&
        0 <= lr[1] &&
        lr[1] < area_length@pre &&
        (l[1] + data_length@pre < area_length@pre =>
           lr[1] == l[1] + data_length@pre) &&
        (l[1] + data_length@pre == area_length@pre =>
           lr[1] == 0) &&
        (l[1] + data_length@pre > area_length@pre =>
           lr[1] == l[1] + data_length@pre - area_length@pre) &&
        lr[2] == 1 &&
        (force@pre != 0 => lr[0] == lr[1]) &&
        (force@pre == 0 => lr[0] == l[0])
*/
{
    int writeidx = state[1];

    if (writeidx + data_length <= area_length) {
        writeidx = (writeidx + data_length) % area_length;
    } else {
        writeidx = data_length - (area_length - writeidx);
    }

    state[1] = writeidx;
    state[2] = 1;

    if (force != 0) {
        state[0] = writeidx;
    }
}
