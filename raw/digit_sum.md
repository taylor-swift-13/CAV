# Digit Sum

## 问题描述

实现一个 Java 静态方法，输入非负整数 `n`，返回十进制各位数字之和。

约定：

- `n >= 0`
- `digit_sum(0) = 0`
- 使用 `% 10` 和 `/ 10` 逐位处理

## Java 要求

- 生成的 Java 类名应为 `DigitSum`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class DigitSum {
    public static int digit_sum(int n) {
        int sum = 0;

        while (n > 0) {
            sum += n % 10;
            n = n / 10;
        }

        return sum;
    }
}
```

## 说明

这是最简单的数位处理题，适合验证“循环中缩小整数 + 累加低位贡献”。
