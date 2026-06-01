# Xizi Fifo Timeslice Init

## 问题描述

实现一个函数，初始化 FIFO 调度策略下的任务时间片字段。

这道题整理自 `kernel/thread/assign_fifo.c` 中的 `FifoTaskTimesliceInit`。为了便于验证，`state[0]` 表示 `origin_timeslice`，`state[1]` 表示 `rest_timeslice`。

约定：

- FIFO 策略不使用时间片
- 初始化后两个字段都应为 `0`

## 正确代码

```c
void xizi_fifo_timeslice_init(int *state) {
    state[0] = 0;
    state[1] = 0;
}
```

## 说明

这道题适合验证结构字段初始化。
