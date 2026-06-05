int xizi_circular_area_data_length(int readidx, int writeidx, int status, int area_length)
/*@ Require
      0 < area_length &&
      0 <= readidx &&
      readidx < area_length &&
      0 <= writeidx &&
      writeidx < area_length &&
      emp
    Ensure
      (readidx@pre == writeidx@pre && status@pre != 0 => __return == area_length@pre) &&
      (readidx@pre == writeidx@pre && status@pre == 0 => __return == 0) &&
      (readidx@pre != writeidx@pre && writeidx@pre >= readidx@pre => __return == writeidx@pre - readidx@pre) &&
      (readidx@pre != writeidx@pre && writeidx@pre < readidx@pre => __return == area_length@pre - (readidx@pre - writeidx@pre)) &&
      emp
*/
{
    if (readidx == writeidx && status != 0) {
        return area_length;
    }

    if (writeidx >= readidx) {
        return writeidx - readidx;
    }

    return area_length - (readidx - writeidx);
}
