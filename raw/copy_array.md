# Copy Array

## 问题描述

实现一个 Java 静态方法，把长度为 `n` 的整数数组 `src` 复制到长度为 `n` 的整数数组 `dst`。

约定：

- `n >= 0`
- `src` 和 `dst` 长度都恰好是 `n`
- 方法读取 `src`，写入 `dst`

## Java 要求

- 生成的 Java 类名应为 `CopyArray`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class CopyArray {
    public static void copy_array(int n, int[] src, int[] dst) {
        int i;

        for (i = 0; i < n; ++i) {
            dst[i] = src[i];
        }
    }
}
```

## 说明

这道题是最基础的双数组扫描：

- 单层循环
- 一个读、一个写
- 不涉及复杂数据结构
- invariant 适合写成“`dst` 已写前缀等于 `src` 对应前缀”
