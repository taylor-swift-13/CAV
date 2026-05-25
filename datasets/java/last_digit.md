# Last Digit

## 问题描述

实现一个函数，返回非负整数 `n` 的十进制个位数字。

约定：

- `n >= 0`。
- 返回值在 `0..9`。
- `n == 0` 时返回 `0`。

## 参考实现

```java
class LastDigit {
    public static int last_digit(int n) {
        return n % 10;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
