# Reverse Digits

## 问题描述

实现一个 Java 静态方法，输入非负整数 `n`，返回它的十进制数字反转后的整数。

约定：

- `n >= 0`
- `reverse_digits(0) = 0`
- 使用 `% 10` 和 `/ 10` 逐位处理

## Java 要求

- 生成的 Java 类名应为 `ReverseDigits`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ReverseDigits {
    public static int reverse_digits(int n) {
        int ans = 0;

        while (n > 0) {
            ans = ans * 10 + n % 10;
            n = n / 10;
        }

        return ans;
    }
}
```

## 说明

这是最简单的数位反转题，适合验证“数位循环 + 累积构造”。
