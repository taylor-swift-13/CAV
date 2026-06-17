int xizi_ready_highest_prio_update(int current_highest, int task_prio)
/*@ Require
      emp
    Ensure
      (task_prio@pre > current_highest@pre => __return == task_prio@pre) &&
      (task_prio@pre <= current_highest@pre => __return == current_highest@pre) &&
      emp
*/
{
    if (task_prio > current_highest) {
        current_highest = task_prio;
    }

    return current_highest;
}
