# Xizi Bitmap Highest Prio

## 问题描述

实现一个函数，输入一个 32 位无符号位图 `bitmap`，返回其中最高置位的下标。

这道题整理自 `kernel/thread/bitmap.c` 中的优先级位图计算逻辑。原实现通过查表计算最高优先级；这里改写成直接扫描，避免表访问和辅助函数调用。

约定：

- 位下标范围是 `0..31`
- 若 `bitmap == 0`，返回 `0`
- 否则返回最大的下标 `i`，满足 `bitmap` 的第 `i` 位为 `1`

## 正确代码

```c
int xizi_bitmap_highest_prio(unsigned int bitmap) {
    int i;

    for (i = 31; i >= 0; --i) {
        if ((bitmap & (1u << i)) != 0u) {
            return i;
        }
    }

    return 0;
}
```

## 说明

这道题适合验证位运算和从高位到低位的扫描逻辑。
