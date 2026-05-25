# Array Find Last Equal

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回最后一个满足 `a[i] == k` 的下标。如果不存在这样的元素，返回 `-1`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 方法不修改数组
- 如果存在多个匹配位置，返回最大的匹配下标

## Java 要求

- 生成的 Java 类名应为 `ArrayFindLastEqual`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayFindLastEqual {
    public static int array_find_last_equal(int n, int[] a, int k) {
        int i;
        int ans = -1;

        for (i = 0; i < n; ++i) {
            if (a[i] == k) {
                ans = i;
            }
        }

        return ans;
    }
}
```

## 说明

这道题适合验证“扫描并维护最后一次命中位置”的模式。
