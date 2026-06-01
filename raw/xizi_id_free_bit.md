# Xizi Id Free Bit

## 问题描述

实现一个函数，释放 ID 位图中的一个 ID。

这道题整理自 `kernel/thread/id.c` 中的 `FreeId`。为了便于验证，`id_map` 用 `int` 数组表示，每个元素只使用低 8 位。

约定：

- `id >= 0`
- `id_map` 至少包含 `id / 8 + 1` 个元素
- 函数清除 `id` 对应的 bit
- 其他 bit 不应被改变

## 正确代码

```c
void xizi_id_free_bit(int *id_map, int id) {
    int index = id / 8;
    int bit = id % 8;

    id_map[index] = id_map[index] & ~(1 << bit);
}
```

## 说明

这道题适合验证按字节分组的位清除操作。
