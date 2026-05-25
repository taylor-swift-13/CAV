# Array Swap Ends

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`。如果 `n >= 2`，交换首元素和尾元素；否则保持不变。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 需要原地修改数组

## Java 要求

- 生成的 Java 类名应为 `ArraySwapEnds`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArraySwapEnds {
    public static void array_swap_ends(int n, int[] a) {
        int t;

        if (n < 2) {
            return;
        }

        t = a[0];
        a[0] = a[n - 1];
        a[n - 1] = t;
    }
}
```

## 说明

这道题适合验证“短分支 + 常量次更新”模式。
