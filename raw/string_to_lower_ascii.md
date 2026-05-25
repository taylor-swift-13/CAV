# String To Lower ASCII

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`，把其中的大写英文字母原地转换为小写英文字母，其他字符保持不变。

约定：

- 输入是合法的 C 风格字符串
- 只处理 ASCII 大写字母 `'A'` 到 `'Z'`
- 方法原地修改字符串

## Java 要求

- 生成的 Java 类名应为 `StringToLowerAscii`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringToLowerAscii {
    public static void string_to_lower_ascii(char[] s) {
        int i = 0;

        while (s[i] != '\0') {
            if (s[i] >= 'A' && s[i] <= 'Z') {
                s[i] = (char)(s[i] + 32);
            }
            i++;
        }
    }
}
```

## 说明

这道题适合验证“字符串原地更新 + 字符范围变换”模式。
