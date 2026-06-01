# Xizi Dataqueue Full

## 问题描述

实现一个函数，判断数据队列是否已满。

这道题整理自 `kernel/thread/data_queue.c` 中 `PushDataqueue` 的满队列判断。

约定：

- `max_len > 1`
- 队列使用空一格策略
- 若 `(rear + 1) % max_len == front`，返回 `1`
- 否则返回 `0`

## 正确代码

```c
int xizi_dataqueue_full(int front, int rear, int max_len) {
    if ((rear + 1) % max_len == front) {
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证空一格循环队列的满条件。
