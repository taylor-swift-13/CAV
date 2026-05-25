# Set Zero

## 问题描述

实现一个 Java 静态方法，把长度为 `n` 的整数数组 `a` 的每个元素都改成 `0`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 方法原地修改数组

## Java 要求

- 生成的 Java 类名应为 `SetZero`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class SetZero {
    public static void set_zero(int n, int[] a) {
        int i;

        for (i = 0; i < n; ++i) {
            a[i] = 0;
        }
    }
}
```

## 说明

这是一道最基础的数组写入题：

- 单层循环
- 原地更新
- 没有分支
- invariant 适合写成“前缀已经全是 `0`，后缀还保持未处理 shape”
