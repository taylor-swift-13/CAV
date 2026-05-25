# String Find Char

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s` 和字符 `c`，返回 `c` 第一次出现的位置；如果不存在，返回 `-1`。

约定：

- 输入是合法的 C 风格字符串
- 方法不修改字符串

## Java 要求

- 生成的 Java 类名应为 `StringFindChar`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringFindChar {
    public static int string_find_char(char[] s, char c) {
        int i = 0;

        while (s[i] != '\0') {
            if (s[i] == c) {
                return i;
            }
            i++;
        }

        return -1;
    }
}
```

## 说明

这道题适合验证“字符串扫描 + 早返回下标”模式。
