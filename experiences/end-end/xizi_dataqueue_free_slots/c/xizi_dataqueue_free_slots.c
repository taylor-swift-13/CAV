int xizi_dataqueue_free_slots(int front, int rear, int max_len)
/*@ Require
      1 < max_len &&
      max_len <= 1073741824 &&
      0 <= front &&
      front < max_len &&
      0 <= rear &&
      rear < max_len &&
      emp
    Ensure
      0 <= __return &&
      __return < max_len@pre &&
      (front@pre <= rear@pre =>
         __return == max_len@pre - 1 - (rear@pre - front@pre)) &&
      (rear@pre < front@pre =>
         __return == front@pre - rear@pre - 1) &&
      emp
*/
{
    int used = (rear - front + max_len) % max_len;
    return max_len - 1 - used;
}
