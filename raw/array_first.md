# Array First Element

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，返回第一个元素。

约定：

- `n >= 1`
- 数组长度恰好是 `n`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayFirst`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayFirst {
    public static int array_first(int n, int[] a) {
        return a[0];
    }
}
```

## 说明

这是最简单的数组读题：

- 没有循环
- 没有分支
- 只需要表达返回值等于数组首元素
