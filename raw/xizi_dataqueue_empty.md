# Xizi Dataqueue Empty

## 问题描述

实现一个函数，判断数据队列是否为空。

这道题整理自 `kernel/thread/data_queue.c` 中 `PopDataqueue` 和 `DataqueuePeak` 对 `front != rear` 的判断。这里抽取为空判断。

约定：

- `front` 是读下标
- `rear` 是写下标
- 若 `front == rear`，返回 `1`
- 否则返回 `0`

## 正确代码

```c
int xizi_dataqueue_empty(int front, int rear) {
    if (front == rear) {
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证循环队列的空条件。
