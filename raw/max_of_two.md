# Max Of Two

## 问题描述

实现一个 Java 静态方法，输入两个整数 `a` 和 `b`，返回两者中的较大值。

约定：

- 如果 `a >= b`，返回 `a`
- 否则返回 `b`
- 方法不修改任何内存

## Java 要求

- 生成的 Java 类名应为 `MaxOfTwo`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class MaxOfTwo {
    public static int max_of_two(int a, int b) {
        if (a >= b) {
            return a;
        } else {
            return b;
        }
    }
}
```

## 说明

这道题适合验证最基础的分支语义：

- 一个 `if/else`
- 无循环
- 无堆内存
- 后置条件可以写成“返回值等于 `a` 或 `b`，且不小于另一个输入”
