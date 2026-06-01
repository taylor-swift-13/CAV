# Xizi Id First Nonfull Byte

## 问题描述

实现一个函数，在 ID 位图中寻找第一个未满的字节位置。

这道题整理自 `kernel/thread/id.c` 中 `AllocId` 的第一段扫描逻辑。

约定：

- `n >= 0`
- `id_map` 有 `n` 个元素
- 每个元素只使用低 8 位
- 若存在 `id_map[i] != 0xff`，返回最小的这样的 `i`
- 若全部为 `0xff`，返回 `-1`

## 正确代码

```c
int xizi_id_first_nonfull_byte(int n, int *id_map) {
    int i;

    for (i = 0; i < n; ++i) {
        if ((id_map[i] & 255) != 255) {
            return i;
        }
    }

    return -1;
}
```

## 说明

这道题适合验证顺序扫描和第一个可用桶定位。
