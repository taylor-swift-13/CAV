# Xizi Stack Range Check

## 问题描述

实现一个函数，判断任务栈指针是否越界。

这道题整理自 `kernel/thread/assignstat.c` 中的栈溢出检查条件。这里用整数地址建模。

约定：

- `sp` 表示当前栈指针地址
- `stack_start` 表示栈起始地址
- `stack_depth` 表示栈空间长度
- 若 `sp <= stack_start` 或 `sp > stack_start + stack_depth`，返回 `1` 表示越界
- 否则返回 `0`

## 正确代码

```c
int xizi_stack_range_check(int sp, int stack_start, int stack_depth) {
    if (sp <= stack_start || sp > stack_start + stack_depth) {
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证边界条件中的开闭区间。
