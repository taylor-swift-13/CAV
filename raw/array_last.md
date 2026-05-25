# Array Last Element

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，返回最后一个元素。

约定：

- `n >= 1`
- 数组长度恰好是 `n`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayLast`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayLast {
    public static int array_last(int n, int[] a) {
        return a[n - 1];
    }
}
```

## 说明

这道题是基础数组索引题：

- 没有循环
- 没有分支
-规格需要保证 `n >= 1`
