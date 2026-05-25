# Array Has Adjacent Equal

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，判断是否存在相邻两个元素相等。如果存在返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法不修改数组
- 返回值只使用 `0` 或 `1`

## Java 要求

- 生成的 Java 类名应为 `ArrayHasAdjacentEqual`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayHasAdjacentEqual {
    public static int array_has_adjacent_equal(int n, int[] a) {
        int i;

        for (i = 1; i < n; ++i) {
            if (a[i] == a[i - 1]) {
                return 1;
            }
        }

        return 0;
    }
}
```

## 说明

这道题适合验证“相邻元素关系 + 提前返回”模式。
