# Xizi Rr Timeslice Tick

## 问题描述

实现一个函数，模拟 RR 剩余时间片调度策略中的一次时钟滴答。

这道题整理自 `kernel/thread/assign_roundrobinremain.c` 中的 `RoundRobinRemainTaskTimesliceUpdate`。这里去掉调度宏调用，只返回是否需要触发调度。

约定：

- `state[0]` 表示 `rest_timeslice`
- `state[1]` 表示 `origin_timeslice`
- `state[2]` 表示 `advance_cnt`
- `max_advance >= 0`
- 每次调用先让 `rest_timeslice` 减一
- 若剩余时间片变为 `0`，则在 `advance_cnt < max_advance` 时递增 `advance_cnt`，再把 `rest_timeslice` 重置为 `origin_timeslice`，并返回 `1`
- 否则返回 `0`

## 正确代码

```c
int xizi_rr_timeslice_tick(int *state, int max_advance) {
    state[0] = state[0] - 1;

    if (state[0] == 0) {
        if (state[2] < max_advance) {
            state[2] = state[2] + 1;
        }

        state[0] = state[1];
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证时间片递减、用尽后重置和计数器饱和前递增。
