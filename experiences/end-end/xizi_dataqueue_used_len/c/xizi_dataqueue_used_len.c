int xizi_dataqueue_used_len(int front, int rear, int max_len)
/*@ Require
      1 < max_len &&
      max_len <= 1073741824 &&
      0 <= front &&
      front < max_len &&
      0 <= rear &&
      rear < max_len &&
      emp
    Ensure
      (rear@pre >= front@pre => __return == rear@pre - front@pre) &&
      (rear@pre < front@pre => __return == max_len@pre - (front@pre - rear@pre)) &&
      emp
*/
{
    return (rear - front + max_len) % max_len;
}
