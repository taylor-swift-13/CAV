# Array Sum Even Indices

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，返回所有偶数下标元素的和。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法不修改数组
- 偶数下标指 `0, 2, 4, ...`

## Java 要求

- 生成的 Java 类名应为 `ArraySumEvenIndices`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArraySumEvenIndices {
    public static int array_sum_even_indices(int n, int[] a) {
        int i;
        int sum = 0;

        for (i = 0; i < n; ++i) {
            if (i % 2 == 0) {
                sum += a[i];
            }
        }

        return sum;
    }
}
```

## 说明

这道题适合验证“数组扫描 + 下标条件 + 累加器”模式。
