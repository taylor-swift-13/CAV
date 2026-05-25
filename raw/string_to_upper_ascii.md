# String To Upper ASCII

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`，把其中所有小写字母转成大写字母，其他字符保持不变。

约定：

- 输入是合法的 C 风格字符串
- 需要原地修改字符串

## Java 要求

- 生成的 Java 类名应为 `StringToUpperAscii`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringToUpperAscii {
    public static void string_to_upper_ascii(char[] s) {
        int i = 0;

        while (s[i] != '\0') {
            if ('a' <= s[i] && s[i] <= 'z') {
                s[i] = (char)(s[i] - 'a' + 'A');
            }
            i++;
        }
    }
}
```

## 说明

这道题适合验证“字符串扫描 + 条件原地更新”模式。
