# Xizi Circular Area Data Length

## 问题描述

实现一个函数，计算环形缓冲区中的有效数据长度。

这道题整理自 `kernel/thread/circular_area.c` 中的 `CircularAreaGetDataLength`。这里直接内联判满条件，不调用其他函数。

约定：

- `area_length > 0`
- `0 <= readidx < area_length`
- `0 <= writeidx < area_length`
- 若 `readidx == writeidx && status != 0`，缓冲区为满，返回 `area_length`
- 否则返回从 `readidx` 到 `writeidx` 的环形距离

## 正确代码

```c
int xizi_circular_area_data_length(int readidx, int writeidx, int status, int area_length) {
    if (readidx == writeidx && status != 0) {
        return area_length;
    }

    return (writeidx - readidx + area_length) % area_length;
}
```

## 说明

这道题适合验证环形下标距离和满状态的特殊处理。
