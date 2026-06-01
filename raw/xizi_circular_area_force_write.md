# Xizi Circular Area Force Write

## 问题描述

实现一个函数，模拟环形缓冲区强制写入后的读写下标状态。

这道题整理自 `kernel/thread/circular_area.c` 中 `CircularAreaWrite` 的 `b_force` 分支。这里去掉数据拷贝，只保留下标更新。

约定：

- `state[0]` 表示 `readidx`
- `state[1]` 表示 `writeidx`
- `state[2]` 表示 `b_status`
- `area_length > 0`
- `0 <= state[1] < area_length`
- 写入 `data_length` 后更新 `writeidx`
- 写入后 `b_status` 置为 `1`
- 若 `force != 0`，则 `readidx` 被设置为新的 `writeidx`

## 正确代码

```c
void xizi_circular_area_force_write(int *state, int data_length, int area_length, int force) {
    int writeidx = state[1];

    if (writeidx + data_length <= area_length) {
        writeidx = (writeidx + data_length) % area_length;
    } else {
        writeidx = data_length - (area_length - writeidx);
    }

    state[1] = writeidx;
    state[2] = 1;

    if (force != 0) {
        state[0] = writeidx;
    }
}
```

## 说明

这道题适合验证强制写入时读指针追随写指针的状态更新。
