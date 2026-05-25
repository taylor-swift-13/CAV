# Array First Negative

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，返回第一个负数元素的下标；如果不存在负数，返回 `-1`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayFirstNegative`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayFirstNegative {
    public static int array_first_negative(int n, int[] a) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] < 0) {
                return i;
            }
        }

        return -1;
    }
}
```

## 说明

这道题适合验证“提前返回 + 前缀中不存在目标元素”模式。
