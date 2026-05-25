# Array Any Negative

## 问题描述

实现一个 Java 静态方法，判断长度为 `n` 的整数数组中是否存在负数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 方法不修改数组
- 如果存在某个下标 `i` 满足 `a[i] < 0`，返回 `1`
- 否则返回 `0`

## Java 要求

- 生成的 Java 类名应为 `ArrayAnyNegative`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayAnyNegative {
    public static int array_any_negative(int n, int[] a) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] < 0) {
                return 1;
            }
        }

        return 0;
    }
}
```

## 说明

这道题适合验证“数组扫描 + 早返回”的存在性判断模式。
