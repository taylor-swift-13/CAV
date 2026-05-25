# Array Equal

## 问题描述

实现一个 Java 静态方法，输入两个长度都为 `n` 的整数数组 `a` 和 `b`，判断它们是否逐项相等。

约定：

- `n >= 0`
- 两个数组长度都恰好是 `n`
- 方法不修改数组
- 如果对所有下标 `i` 都有 `a[i] == b[i]`，返回 `1`
- 否则返回 `0`

## Java 要求

- 生成的 Java 类名应为 `ArrayEqual`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayEqual {
    public static int array_equal(int n, int[] a, int[] b) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] != b[i]) {
                return 0;
            }
        }

        return 1;
    }
}
```

## 说明

这道题适合验证“双数组同步扫描”模式：

- 两个输入数组
- 只读比较
- 发现不等后立即返回
