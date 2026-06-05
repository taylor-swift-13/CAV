int xizi_ready_bitmap_empty(unsigned int ready_group)
/*@ Require
      emp
    Ensure
      (ready_group@pre == 0 => __return == 1) &&
      (ready_group@pre != 0 => __return == 0) &&
      emp
*/
{
    if (ready_group == 0u) {
        return 1;
    }

    return 0;
}
