# Array Clamp Nonnegative

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`。把所有负数元素改成 `0`，非负元素保持不变。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 需要原地修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayClampNonnegative`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayClampNonnegative {
    public static void array_clamp_nonnegative(int n, int[] a) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] < 0) {
                a[i] = 0;
            }
        }
    }
}
```

## 说明

这道题适合验证“条件式原地修正”模式。
