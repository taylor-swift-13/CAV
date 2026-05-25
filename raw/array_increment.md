# Array Increment

## 问题描述

实现一个 Java 静态方法，把长度为 `n` 的整数数组 `a` 的每个元素都加一。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 每个元素加一后仍在 Java int 范围内
- 方法原地修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayIncrement`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayIncrement {
    public static void array_increment(int n, int[] a) {
        int i;

        for (i = 0; i < n; ++i) {
            a[i] = a[i] + 1;
        }
    }
}
```

## 说明

这道题比 `set_zero` 多一步读后写：

- 单层循环
- 原地更新
- 需要元素范围前置条件保证 `a[i] + 1` 不溢出
- invariant 适合写成“已处理前缀等于原数组前缀逐项加一”
