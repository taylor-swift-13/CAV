# Array Contains

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a` 和整数 `k`，判断数组中是否存在等于 `k` 的元素。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 方法不修改数组
- 若存在某个下标 `i` 满足 `a[i] == k`，返回 `1`
- 否则返回 `0`

## Java 要求

- 生成的 Java 类名应为 `ArrayContains`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayContains {
    public static int array_contains(int n, int[] a, int k) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] == k) {
                return 1;
            }
        }

        return 0;
    }
}
```

## 说明

这道题适合验证最基础的“扫描并返回布尔结果”模式：

- 单层循环
- 只读数组
- 命中后立即返回
