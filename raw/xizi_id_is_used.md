# Xizi Id Is Used

## 问题描述

实现一个函数，判断 ID 位图中的某个 ID 是否已占用。

这道题整理自 `kernel/thread/id.c` 的 ID 位图布局。`id_map` 用 `int` 数组表示，每个元素只使用低 8 位。

约定：

- `id >= 0`
- `id_map[id / 8]` 的第 `id % 8` 位表示该 ID 状态
- bit 为 `1` 表示已占用，返回 `1`
- bit 为 `0` 表示空闲，返回 `0`

## 正确代码

```c
int xizi_id_is_used(int *id_map, int id) {
    int entry = id_map[id / 8];
    int mask = 1 << (id % 8);

    if ((entry & mask) != 0) {
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证位图查询。
