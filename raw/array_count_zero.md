# Array Count Zero

## 问题描述

实现一个 Java 静态方法，统计长度为 `n` 的整数数组中等于 `0` 的元素个数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 方法不修改数组
- 返回值等于数组中满足 `a[i] == 0` 的下标数量

## Java 要求

- 生成的 Java 类名应为 `ArrayCountZero`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayCountZero {
    public static int array_count_zero(int n, int[] a) {
        int i;
        int count = 0;

        for (i = 0; i < n; ++i) {
            if (a[i] == 0) {
                count++;
            }
        }

        return count;
    }
}
```

## 说明

这道题适合验证“条件计数”的数组扫描模式。
