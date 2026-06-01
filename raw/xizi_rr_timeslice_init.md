# Xizi Rr Timeslice Init

## 问题描述

实现一个函数，初始化 RR 调度策略下的任务时间片字段。

这道题整理自 `kernel/thread/assign_roundrobin.c` 中的 `RoundRobinTaskTimesliceInit`。为了便于验证，`state[0]` 表示 `origin_timeslice`，`state[1]` 表示 `rest_timeslice`。

约定：

- RR 策略初始时间片为 `10`
- 初始化后 `origin_timeslice == 10`
- 初始化后 `rest_timeslice == 10`

## 正确代码

```c
void xizi_rr_timeslice_init(int *state) {
    state[0] = 10;
    state[1] = 10;
}
```

## 说明

这道题适合验证固定常量初始化。
