int xizi_circular_area_state(int readidx, int writeidx, int status)
/*@ Require
      emp
    Ensure
      (readidx@pre == writeidx@pre && status@pre != 0 => __return == 1) &&
      (readidx@pre == writeidx@pre && status@pre == 0 => __return == -1) &&
      (readidx@pre != writeidx@pre => __return == 0) &&
      emp
*/
{
    if (readidx == writeidx && status != 0) {
        return 1;
    }

    if (readidx == writeidx && status == 0) {
        return -1;
    }

    return 0;
}
