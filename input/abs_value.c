int abs_value(int x)
/*@ Require
      x >= -2147483647 &&
      emp
    Ensure
      (x@pre >= 0 => __return == x@pre) &&
      (x@pre <  0 => __return == -x@pre) &&
      emp
*/
{
    if (x >= 0) {
        return x;
    } else {
        return -x;
    }
}
