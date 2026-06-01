int xizi_stack_range_check(int sp, int stack_start, int stack_depth)
/*@ Require
      0 <= stack_depth &&
      -2147483648 <= stack_start + stack_depth &&
      stack_start + stack_depth <= 2147483647 &&
      emp
    Ensure
      ((__return == 1 &&
        (sp@pre <= stack_start@pre ||
         sp@pre > stack_start@pre + stack_depth@pre)) ||
       (__return == 0 &&
        stack_start@pre < sp@pre &&
        sp@pre <= stack_start@pre + stack_depth@pre)) &&
      emp
*/
{
    if (sp <= stack_start || sp > stack_start + stack_depth) {
        return 1;
    }

    return 0;
}
