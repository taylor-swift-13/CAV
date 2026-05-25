# Array Add

## 问题描述

实现一个 Java 静态方法，输入两个长度为 `n` 的整数数组 `a`、`b`，以及长度为 `n` 的输出数组 `out`。把逐项求和结果写入 `out`。

约定：

- `n >= 0`
- 三个数组长度都恰好是 `n`
- 方法不返回值
- 对每个下标 `i`，执行后都有 `out[i] == a[i] + b[i]`

## Java 要求

- 生成的 Java 类名应为 `ArrayAdd`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayAdd {
    public static void array_add(int n, int[] a, int[] b, int[] out) {
        int i;

        for (i = 0; i < n; ++i) {
            out[i] = a[i] + b[i];
        }
    }
}
```

## 说明

这道题适合验证“两个输入数组 + 一个输出数组”的最基础写入模式：

- 单层循环
- 输出数组逐步填充
- 输入数组保持不变
