int xizi_circular_area_write_advance(int writeidx, int data_length, int area_length)
/*@ Require
      0 < area_length &&
      0 <= writeidx &&
      writeidx < area_length &&
      0 <= data_length &&
      data_length <= area_length &&
      writeidx + data_length <= 2147483647 &&
      emp
    Ensure
      (writeidx@pre + data_length@pre < area_length@pre =>
         __return == writeidx@pre + data_length@pre) &&
      (writeidx@pre + data_length@pre == area_length@pre =>
         __return == 0) &&
      (writeidx@pre + data_length@pre > area_length@pre =>
         __return == writeidx@pre + data_length@pre - area_length@pre) &&
      emp
*/
{
    if (writeidx + data_length <= area_length) {
        return (writeidx + data_length) % area_length;
    } else {
        return data_length - (area_length - writeidx);
    }
}
