# Xizi Ready Highest Prio Update

## 问题描述

实现一个函数，插入任务后更新 ready 表记录的最高优先级。

这道题整理自 `kernel/thread/assignstat.c` 中 `AssignPolicyInsert` 末尾对 `highest_prio` 的更新逻辑。

约定：

- 数值越大表示优先级越高
- `current_highest` 是 ready 表当前记录的最高优先级
- `task_prio` 是新插入任务的优先级
- 返回更新后的最高优先级

## 正确代码

```c
int xizi_ready_highest_prio_update(int current_highest, int task_prio) {
    if (task_prio > current_highest) {
        current_highest = task_prio;
    }

    return current_highest;
}
```

## 说明

这道题适合验证单字段状态的条件更新。
