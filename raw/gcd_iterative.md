# GCD Iterative

## 问题描述

实现一个 Java 静态方法，输入两个非负整数 `a` 和 `b`，返回它们的最大公约数。

约定：

- `a >= 0`
- `b >= 0`
- `a` 和 `b` 不同时为 `0`
- 使用 Euclid 算法

## Java 要求

- 生成的 Java 类名应为 `GcdIterative`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class GcdIterative {
    public static int gcd_iterative(int a, int b) {
        int r;

        while (b != 0) {
            r = a % b;
            a = b;
            b = r;
        }

        return a;
    }
}
```

## 说明

这是最基础的数论循环题，适合验证“Euclid 算法保持 gcd 不变”。
