# Add Two Numbers

## 问题描述

实现一个 Java 静态方法，输入两个整数 `a` 和 `b`，返回它们的和。

约定：

- 输入都在 Java int 范围内。
- 结果也保证在 Java int 范围内。
- 方法不读写额外状态。

## Java 要求

- 生成的 Java 类名应为 `AddTwo`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class AddTwo {
    public static int add_two(int a, int b) {
        return a + b;
    }
}
```

## 说明

这是一道最简单的纯标量方法：

- 没有循环
- 没有数组
- 没有额外内存资源
- 后置条件只需要表达返回值等于 `a + b`
