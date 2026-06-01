# Xizi Dataqueue Used Len

## 问题描述

实现一个函数，计算循环数据队列中已有元素数量。

这道题整理自 `kernel/thread/data_queue.c` 的 `front` 和 `rear` 环形下标模型。

约定：

- `max_len > 1`
- `0 <= front < max_len`
- `0 <= rear < max_len`
- 返回从 `front` 到 `rear` 的环形距离

## 正确代码

```c
int xizi_dataqueue_used_len(int front, int rear, int max_len) {
    return (rear - front + max_len) % max_len;
}
```

## 说明

这道题适合验证循环队列中元素个数的模运算公式。
