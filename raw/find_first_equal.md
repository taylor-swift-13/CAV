# Find First Equal

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回第一个等于 `k` 的下标；如果不存在，返回 `-1`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `FindFirstEqual`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class FindFirstEqual {
    public static int find_first_equal(int n, int[] a, int k) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] == k) {
                return i;
            }
        }

        return -1;
    }
}
```

## 说明

这道题适合验证最基础的“扫描直到命中”模式：

- 单层循环
- 循环内早返回
- 不修改数组
