# Array Scale

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`、一个整数 `k`，以及长度为 `n` 的输出数组 `out`。把 `a` 中每个元素乘以 `k` 后写入 `out`。

约定：

- `n >= 0`
- `a` 和 `out` 长度都恰好是 `n`
- 方法不返回值
- 对每个下标 `i`，执行后都有 `out[i] == a[i] * k`

## Java 要求

- 生成的 Java 类名应为 `ArrayScale`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayScale {
    public static void array_scale(int n, int[] a, int k, int[] out) {
        int i;

        for (i = 0; i < n; ++i) {
            out[i] = a[i] * k;
        }
    }
}
```

## 说明

这道题适合验证“只读输入数组 + 标量参数 + 输出数组”的基础循环模式。
