# Array Count Greater Than K

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回数组中严格大于 `k` 的元素个数。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayCountGreaterThanK`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayCountGreaterThanK {
    public static int array_count_greater_than_k(int n, int[] a, int k) {
        int i;
        int cnt = 0;

        for (i = 0; i < n; ++i) {
            if (a[i] > k) {
                cnt++;
            }
        }

        return cnt;
    }
}
```

## 说明

这道题适合验证“数组扫描 + 阈值条件计数”模式。
