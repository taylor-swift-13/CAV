# Array Remove Value To Output

## 问题描述

实现一个 Java 静态方法，把数组中所有不等于给定值 `k` 的元素按原顺序复制到输出数组，并返回复制的元素个数。

约定：
- `n` 表示输入数组长度，`n >= 0`。
- `a` 表示长度至少为 `n` 的输入数组。
- `out` 表示长度至少为 `n` 的输出数组。
- 输入数组 `a` 不需要被修改。

## Java 要求

- 生成的 Java 类名应为 `ArrayRemoveValueToOutput`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayRemoveValueToOutput {
    public static int array_remove_value_to_output(int n, int[] a, int k, int[] out) {
        int write = 0;
        int i = 0;
        while (i < n) {
            if (a[i] != k) {
                out[write] = a[i];
                write++;
            }
            i++;
        }
        return write;
    }
}
```

## 说明

`write` 始终表示输出数组下一个可写位置。每遇到一个不等于 `k` 的元素，就把它复制到输出数组并推进 `write`。
