# Is Prime Simple

## 问题描述

实现一个 Java 静态方法，输入整数 `n`，判断 `n` 是否为质数。如果是返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- 质数定义为大于 `1` 且只有 `1` 和自身两个正因子的整数
- 返回值只使用 `0` 或 `1`

## Java 要求

- 生成的 Java 类名应为 `IsPrimeSimple`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class IsPrimeSimple {
    public static int is_prime_simple(int n) {
        int d;

        if (n < 2) {
            return 0;
        }

        for (d = 2; d < n; ++d) {
            if (n % d == 0) {
                return 0;
            }
        }

        return 1;
    }
}
```

## 说明

这是最简单的质数判断，适合验证“逐个排除因子 + 提前返回”。
