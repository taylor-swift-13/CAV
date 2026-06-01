# Xizi Circular Area Read Advance

## 问题描述

实现一个函数，计算环形缓冲区读取 `data_length` 个字节后的新读下标。

这道题整理自 `kernel/thread/circular_area.c` 中读取路径对 `readidx` 的更新。这里只保留下标算法，不包含拷贝和函数调用。

约定：

- `area_length > 0`
- `0 <= readidx < area_length`
- `0 <= data_length <= area_length`
- 返回读取后的新 `readidx`
- 若读取跨过尾部，则从头部继续计数

## 正确代码

```c
int xizi_circular_area_read_advance(int readidx, int data_length, int area_length) {
    if (readidx + data_length <= area_length) {
        return (readidx + data_length) % area_length;
    } else {
        return data_length - (area_length - readidx);
    }
}
```

## 说明

这道题适合验证环形缓冲区读指针跨尾部时的分段更新。
