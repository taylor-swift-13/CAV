#include "../../verification_stdlib.h"

int xizi_dataqueue_empty(int front, int rear)
/*@ Require
      emp
    Ensure
      ((__return == 1 &&
        front@pre == rear@pre) ||
       (__return == 0 &&
        front@pre != rear@pre)) &&
      emp
*/
{
    if (front == rear) {
        return 1;
    }

    return 0;
}
