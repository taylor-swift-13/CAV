# Array All Positive

## 问题描述

实现一个 Java 静态方法，判断长度为 `n` 的整数数组 `a` 是否全部大于 `0`。

约定：

- 如果所有元素都大于 `0`，返回 `1`
- 只要有一个元素小于等于 `0`，返回 `0`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayAllPositive`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayAllPositive {
    public static int array_all_positive(int n, int[] a) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] <= 0) {
                return 0;
            }
        }

        return 1;
    }
}
```

## 说明

这道题是最基础的全称检查题：

- 单层循环
- 循环内早返回
- 不修改数组
