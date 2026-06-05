int xizi_avl_balance_factor(int left_height, int right_height)
/*@ Require
      0 <= left_height &&
      0 <= right_height &&
      emp
    Ensure
      __return == left_height@pre - right_height@pre &&
      emp
*/
{
    return left_height - right_height;
}
