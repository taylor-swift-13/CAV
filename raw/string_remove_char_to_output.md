# String Remove Char To Output

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`、输出数组 `out` 和字符 `c`。把 `s` 中所有不等于 `c` 的字符按原顺序复制到 `out`，最后写入结尾字符 `'\0'`，返回输出字符串的长度。

约定：

- 输入 `s` 是合法的 C 风格字符串
- `out` 有足够空间保存结果和结尾字符
- 方法不修改 `s`

## Java 要求

- 生成的 Java 类名应为 `StringRemoveCharToOutput`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringRemoveCharToOutput {
    public static int string_remove_char_to_output(char[] s, char[] out, char c) {
        int i = 0;
        int j = 0;

        while (s[i] != '\0') {
            if (s[i] != c) {
                out[j] = s[i];
                j++;
            }
            i++;
        }

        out[j] = '\0';
        return j;
    }
}
```

## 说明

这道题适合验证“双下标字符串扫描 + 条件复制 + 输出长度”模式。
