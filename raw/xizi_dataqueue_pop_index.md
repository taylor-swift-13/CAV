# Xizi Dataqueue Pop Index

## 问题描述

实现一个函数，模拟数据队列出队时的下标更新和槽位读取。

这道题整理自 `kernel/thread/data_queue.c` 中的 `PopDataqueue`。这里去掉信号量、锁和日志，只保留循环队列算法。

约定：

- `max_len > 1`
- `0 <= front < max_len`
- `0 <= rear < max_len`
- 队列空的条件是 `front == rear`
- 若队列非空，把 `data[front]` 和 `length[front]` 写入 `out_value[0]`、`out_size[0]`，并返回新的 `front`
- 若队列为空，不修改输出数组，返回原 `front`

## 正确代码

```c
int xizi_dataqueue_pop_index(int front, int rear, int max_len, int *data, int *length, int *out_value, int *out_size) {
    if (front != rear) {
        out_value[0] = data[front];
        out_size[0] = length[front];
        front = (front + 1) % max_len;
    }

    return front;
}
```

## 说明

这道题适合验证循环队列的出队读取和读下标前进。
