int xizi_circular_area_read_advance(int readidx, int data_length, int area_length)
/*@ Require
      0 < area_length &&
      area_length <= 1073741824 &&
      0 <= readidx &&
      readidx < area_length &&
      0 <= data_length &&
      data_length <= area_length &&
      emp
    Ensure
      0 <= __return &&
      __return < area_length@pre &&
      __return == (readidx@pre + data_length@pre) % area_length@pre &&
      emp
*/
{
    if (readidx + data_length <= area_length) {
        return (readidx + data_length) % area_length;
    } else {
        return data_length - (area_length - readidx);
    }
}
