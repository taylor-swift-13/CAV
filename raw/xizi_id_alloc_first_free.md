# Xizi Id Alloc First Free

## 问题描述

实现一个函数，从 ID 位图中分配第一个空闲 ID。

这道题整理自 `kernel/thread/id.c` 中的 `AllocId`。为了便于验证，`id_map` 用 `int` 数组表示，每个元素只使用低 8 位。

约定：

- `id_max >= 0`
- `id_map` 至少有 `(id_max + 7) / 8` 个元素
- `id_map[i]` 的低 8 位表示 8 个 ID 的占用状态，低位对应较小 ID
- bit 为 `1` 表示已占用，bit 为 `0` 表示空闲
- 若存在空闲 ID，则设置对应 bit 并返回该 ID
- 若不存在可分配 ID，返回 `-1`

## 正确代码

```c
int xizi_id_alloc_first_free(int id_max, int *id_map) {
    int index = 0;
    int end = (id_max + 7) / 8;
    int id;
    int entry;

    for (index = 0; index < end; ++index) {
        if ((id_map[index] & 255) != 255) {
            break;
        }
    }
    if (index == end) {
        return -1;
    }

    id = index * 8;
    entry = id_map[index] & 255;
    while ((entry & 1) != 0) {
        id++;
        entry = entry >> 1;
    }

    if (id >= id_max) {
        return -1;
    }

    id_map[index] = id_map[index] | (1 << (id % 8));
    return id;
}
```

## 说明

这道题适合验证位图扫描、低位优先分配和原地更新。
