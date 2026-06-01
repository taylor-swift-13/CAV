# Xizi Circular Area Write Advance

## 问题描述

实现一个函数，计算环形缓冲区写入 `data_length` 个字节后的新写下标。

这道题整理自 `kernel/thread/circular_area.c` 中写入路径对 `writeidx` 的更新。这里只保留下标算法，不包含拷贝和函数调用。

约定：

- `area_length > 0`
- `0 <= writeidx < area_length`
- `0 <= data_length <= area_length`
- 返回写入后的新 `writeidx`
- 若写入跨过尾部，则从头部继续计数

## 正确代码

```c
int xizi_circular_area_write_advance(int writeidx, int data_length, int area_length) {
    if (writeidx + data_length <= area_length) {
        return (writeidx + data_length) % area_length;
    } else {
        return data_length - (area_length - writeidx);
    }
}
```

## 说明

这道题适合验证环形缓冲区写指针跨尾部时的分段更新。
