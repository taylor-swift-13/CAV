# Rotate Left By One

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，把它循环左移一位。

约定：

- `n >= 1`
- 数组长度恰好是 `n`
- 需要原地修改数组
- 执行后：
  - 原来的 `a[1]` 变成新的 `a[0]`
  - 原来的 `a[n - 1]` 变成新的 `a[n - 2]`
  - 原来的 `a[0]` 变成新的 `a[n - 1]`

## Java 要求

- 生成的 Java 类名应为 `RotateLeftByOne`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class RotateLeftByOne {
    public static void rotate_left_by_one(int n, int[] a) {
        int i;
        int first = a[0];

        for (i = 0; i + 1 < n; ++i) {
            a[i] = a[i + 1];
        }
        a[n - 1] = first;
    }
}
```

## 说明

这道题适合验证“原地覆盖 + 最后补回暂存值”模式。
