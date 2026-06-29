int clamp_int(int x, int lo, int hi)
/*@ Require
      lo <= hi &&
      emp
    Ensure
      (x@pre <  lo@pre             => __return == lo@pre) &&
      (x@pre >  hi@pre             => __return == hi@pre) &&
      (lo@pre <= x@pre && x@pre <= hi@pre => __return == x@pre) &&
      emp
*/
{
    if (x < lo) {
        return lo;
    }
    if (x > hi) {
        return hi;
    }
    return x;
}
