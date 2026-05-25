# Partition Nonnegative

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，原地调整数组，使所有负数位于前面，所有非负数位于后面，返回负数的个数。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法原地修改数组
- 不要求保持元素原有相对顺序

## Java 要求

- 生成的 Java 类名应为 `PartitionNonnegative`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class PartitionNonnegative {
    public static int partition_nonnegative(int n, int[] a) {
        int i = 0;
        int j = n - 1;
        int tmp;

        while (i <= j) {
            if (a[i] < 0) {
                i++;
            } else {
                tmp = a[i];
                a[i] = a[j];
                a[j] = tmp;
                j--;
            }
        }

        return i;
    }
}
```

## 说明

这是经典 partition 题，适合验证“双指针区间收缩 + 分区性质”。
