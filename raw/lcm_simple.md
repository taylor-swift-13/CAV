# LCM Simple

## 问题描述

实现一个 Java 静态方法，输入两个正整数 `a` 和 `b`，返回它们的最小公倍数。

约定：

- `a > 0`
- `b > 0`
- 使用简单枚举，从 `a` 开始每次加 `a`，直到找到能被 `b` 整除的数

## Java 要求

- 生成的 Java 类名应为 `LcmSimple`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class LcmSimple {
    public static int lcm_simple(int a, int b) {
        int x = a;

        while (x % b != 0) {
            x = x + a;
        }

        return x;
    }
}
```

## 说明

这是最简单的最小公倍数枚举题，适合验证“循环保持倍数 + 找到整除条件”。
