# Array Is Strictly Increasing

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，判断数组是否严格递增。如果对所有相邻下标都有 `a[i - 1] < a[i]`，返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 空数组和单元素数组都视为严格递增
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayIsStrictlyIncreasing`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayIsStrictlyIncreasing {
    public static int array_is_strictly_increasing(int n, int[] a) {
        int i;

        for (i = 1; i < n; ++i) {
            if (a[i - 1] >= a[i]) {
                return 0;
            }
        }

        return 1;
    }
}
```

## 说明

这道题适合验证“相邻有序性 + 反例提前返回”模式。
