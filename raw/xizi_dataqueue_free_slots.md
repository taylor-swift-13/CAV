# Xizi Dataqueue Free Slots

## 问题描述

实现一个函数，计算空一格循环数据队列还可写入的槽位数量。

这道题整理自 `kernel/thread/data_queue.c` 中 `max_len - 1` 个空白信号量的设计。

约定：

- `max_len > 1`
- 队列最多存放 `max_len - 1` 个元素
- 返回当前还可写入的元素数量

## 正确代码

```c
int xizi_dataqueue_free_slots(int front, int rear, int max_len) {
    int used = (rear - front + max_len) % max_len;
    return max_len - 1 - used;
}
```

## 说明

这道题适合验证空一格队列的容量计算。
