# Count Digits

## 问题描述

实现一个 Java 静态方法，输入非负整数 `n`，返回它的十进制位数。

约定：

- `n >= 0`
- `count_digits(0) = 1`
- 对正数使用 `/ 10` 循环计数

## Java 要求

- 生成的 Java 类名应为 `CountDigits`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class CountDigits {
    public static int count_digits(int n) {
        int cnt = 0;

        if (n == 0) {
            return 1;
        }

        while (n > 0) {
            cnt++;
            n = n / 10;
        }

        return cnt;
    }
}
```

## 说明

这是最简单的十进制位数统计题。
