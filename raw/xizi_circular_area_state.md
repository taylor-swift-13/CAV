# Xizi Circular Area State

## 问题描述

实现一个函数，判断环形缓冲区状态。

这道题整理自 `kernel/thread/circular_area.c` 中的 `CircularAreaIsFull` 和 `CircularAreaIsEmpty`。原结构中的 `readidx`、`writeidx` 和 `b_status` 用整数参数表示。

约定：

- `status != 0` 表示最近一次操作使缓冲区处于“有数据”状态
- 若 `readidx == writeidx && status != 0`，返回 `1` 表示满
- 若 `readidx == writeidx && status == 0`，返回 `-1` 表示空
- 其他情况返回 `0`

## 正确代码

```c
int xizi_circular_area_state(int readidx, int writeidx, int status) {
    if (readidx == writeidx && status != 0) {
        return 1;
    }

    if (readidx == writeidx && status == 0) {
        return -1;
    }

    return 0;
}
```

## 说明

这道题适合验证环形缓冲区中同一组下标如何借助状态位区分满和空。
