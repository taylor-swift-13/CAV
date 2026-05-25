# String Count Digits

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`，统计其中数字字符的个数。

约定：

- 输入是合法的 C 风格字符串
- 数字字符范围是 `'0'` 到 `'9'`
- 方法不修改字符串

## Java 要求

- 生成的 Java 类名应为 `StringCountDigits`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringCountDigits {
    public static int string_count_digits(char[] s) {
        int i = 0;
        int cnt = 0;

        while (s[i] != '\0') {
            if (s[i] >= '0' && s[i] <= '9') {
                cnt++;
            }
            i++;
        }

        return cnt;
    }
}
```

## 说明

这道题适合验证“字符串扫描 + 字符范围计数”模式。
