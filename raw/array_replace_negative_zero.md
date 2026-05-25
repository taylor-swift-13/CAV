# Array Replace Negative Zero

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，把所有负数原地改为 `0`，非负数保持不变。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法会修改数组 `a`

## Java 要求

- 生成的 Java 类名应为 `ArrayReplaceNegativeZero`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayReplaceNegativeZero {
    public static void array_replace_negative_zero(int n, int[] a) {
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

这道题适合验证“原地数组更新 + 条件保持原值”模式。
