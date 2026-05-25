# String First Char

## 问题描述

实现一个 Java 静态方法，输入一个非空字符串 `s`，返回它的第一个字符。

约定：

- `s` 是合法的以 `'\0'` 结尾的字符串
- `s` 不是空串
- 方法不修改字符串

## Java 要求

- 生成的 Java 类名应为 `StringFirstChar`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringFirstChar {
    public static char string_first_char(char[] s) {
        return s[0];
    }
}
```

## 说明

这是最简单的字符串读取题：

- 没有循环
- 没有分支
- 只需要保证字符串非空
