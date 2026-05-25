# Fibonacci

## 问题描述

实现一个 Java 静态方法，输入整数 `n`，返回第 `n` 个 Fibonacci 数。

约定：

- `n >= 0`
- `fib(0) = 0`
- `fib(1) = 1`
- 对 `n >= 2`，`fib(n) = fib(n - 1) + fib(n - 2)`

## Java 要求

- 生成的 Java 类名应为 `Fibonacci`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class Fibonacci {
    public static int fibonacci(int n) {
        int i;
        int a = 0;
        int b = 1;
        int c;

        if (n == 0) {
            return 0;
        }

        for (i = 2; i <= n; ++i) {
            c = a + b;
            a = b;
            b = c;
        }

        return b;
    }
}
```

## 说明

这是最简单的动态规划题之一，适合验证“两状态滚动数组”的循环不变量。
