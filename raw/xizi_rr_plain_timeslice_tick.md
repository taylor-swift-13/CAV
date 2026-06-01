# Xizi Rr Plain Timeslice Tick

## 问题描述

实现一个函数，模拟普通 RR 调度策略中的一次时间片滴答。

这道题整理自 `kernel/thread/assign_roundrobin.c` 中的 `RoundRobinTaskTimesliceUpdate`。这里去掉调度宏调用，只返回是否需要触发调度。

约定：

- `state[0]` 表示 `rest_timeslice`
- `state[1]` 表示 `origin_timeslice`
- 每次调用先让 `rest_timeslice` 减一
- 若剩余时间片变为 `0`，重置为 `origin_timeslice` 并返回 `1`
- 否则返回 `0`

## 正确代码

```c
int xizi_rr_plain_timeslice_tick(int *state) {
    state[0] = state[0] - 1;

    if (state[0] == 0) {
        state[0] = state[1];
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证递减、归零检测和重置。
