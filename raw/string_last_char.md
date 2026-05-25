# String Last Char

## 问题描述

实现一个 Java 静态方法，输入一个非空字符串 `s`，返回它的最后一个字符。

约定：

- `s` 是合法的以 `'\0'` 结尾的字符串
- `s` 不是空串
- 方法不修改字符串

## Java 要求

- 生成的 Java 类名应为 `StringLastChar`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringLastChar {
    public static char string_last_char(char[] s) {
        int i = 0;

        while (s[i + 1] != '\0') {
            i++;
        }

        return s[i];
    }
}
```

## 说明

这道题是最基础的字符串尾字符扫描：

- 单层循环
- 不修改字符串
- 需要保证字符串非空
