# Xizi Dataqueue Push Index

## 问题描述

实现一个函数，模拟数据队列入队时的下标更新和槽位写入。

这道题整理自 `kernel/thread/data_queue.c` 中的 `PushDataqueue`。这里去掉信号量、锁和日志，只保留循环队列算法。

约定：

- `max_len > 1`
- `0 <= front < max_len`
- `0 <= rear < max_len`
- 队列满的条件是 `(rear + 1) % max_len == front`
- 若队列未满，把 `value` 和 `size` 写入 `data[rear]`、`length[rear]`，并返回新的 `rear`
- 若队列已满，不修改数组，返回原 `rear`

## 正确代码

```c
int xizi_dataqueue_push_index(int front, int rear, int max_len, int *data, int *length, int value, int size) {
    if ((rear + 1) % max_len != front) {
        data[rear] = value;
        length[rear] = size;
        rear = (rear + 1) % max_len;
    }

    return rear;
}
```

## 说明

这道题适合验证“空一格”循环队列的入队边界条件。
