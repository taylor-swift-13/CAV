# Is Sorted Nondecreasing

## 问题描述

实现一个 Java 静态方法，判断长度为 `n` 的整数数组 `a` 是否是非递减的。

约定：

- 如果对所有 `0 <= i < n - 1` 都有 `a[i] <= a[i + 1]`，返回 `1`
- 否则返回 `0`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `IsSortedNondecreasing`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class IsSortedNondecreasing {
    public static int is_sorted_nondecreasing(int n, int[] a) {
        int i;

        for (i = 0; i + 1 < n; ++i) {
            if (a[i] > a[i + 1]) {
                return 0;
            }
        }

        return 1;
    }
}
```

## 说明

这道题适合验证“扫描直到发现反例”的模式：

- 单层循环
- 循环内早返回
- 不修改数组
