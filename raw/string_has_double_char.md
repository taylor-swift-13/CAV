# String Has Double Char

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`，判断是否存在两个相邻字符相同。如果存在返回 `1`，否则返回 `0`。

约定：

- 输入是合法的 C 风格字符串
- 方法不修改字符串
- 返回值只使用 `0` 或 `1`

## Java 要求

- 生成的 Java 类名应为 `StringHasDoubleChar`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringHasDoubleChar {
    public static int string_has_double_char(char[] s) {
        int i = 1;

        while (s[i] != '\0') {
            if (s[i] == s[i - 1]) {
                return 1;
            }
            i++;
        }

        return 0;
    }
}
```

## 说明

这道题适合验证“字符串相邻字符关系 + 提前返回”模式。
