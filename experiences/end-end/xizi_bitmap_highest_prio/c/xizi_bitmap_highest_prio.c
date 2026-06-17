/*@ Extern Coq (xizi_bitmap_highest_prio_spec : Z -> Z -> Prop) */
/*@ Import Coq Require Import xizi_bitmap_highest_prio */

int xizi_bitmap_highest_prio(unsigned int bitmap)
/*@ Require
      emp
    Ensure
      xizi_bitmap_highest_prio_spec(bitmap@pre, __return) &&
      emp
*/
{
    int i;

    for (i = 31; i >= 0; --i) {
        if ((bitmap & (1u << i)) != 0u) {
            return i;
        }
    }

    return 0;
}
