# Is Between Inclusive

## 问题描述

实现一个函数，判断整数 `x` 是否位于闭区间 `[lo, hi]` 内。

约定：

- `lo <= hi`。
- 如果 `lo <= x <= hi` 返回 `1`。
- 否则返回 `0`。

## 参考实现

```c
int is_between_inclusive(int x, int lo, int hi) {
    return x >= lo && x <= hi;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
