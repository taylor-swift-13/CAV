int xizi_dataqueue_empty(int front, int rear)
/*@ Require
      emp
    Ensure
      (front@pre == rear@pre => __return == 1) &&
      (front@pre != rear@pre => __return == 0) &&
      emp
*/
{
    if (front == rear) {
        return 1;
    }

    return 0;
}
