# Xizi Ready Bitmap Empty

## 问题描述

实现一个函数，判断调度 ready 位图是否为空。

这道题整理自 `kernel/thread/assignstat.c` 中的 `JudgeAssignReadyBitmapIsEmpty`，只保留对 `priority_ready_group` 的判断。

约定：

- `ready_group == 0` 表示没有任何优先级处于 ready 状态
- 返回 `1` 表示为空
- 返回 `0` 表示非空

## 正确代码

```c
int xizi_ready_bitmap_empty(unsigned int ready_group) {
    if (ready_group == 0u) {
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证调度位图的零值判空逻辑。
