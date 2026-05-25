# String Set A

## 问题描述

实现一个 Java 静态方法，把长度为 `n` 的字符数组 `s` 的前 `n` 个位置都写成字符 `'a'`，并在最后写入 `'\0'`。

约定：

- `n >= 0`
- `s` 至少有 `n + 1` 个字符空间
- 方法会写入 `n` 个 `'a'`，再写一个结尾 `'\0'`

## Java 要求

- 生成的 Java 类名应为 `StringSetA`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringSetA {
    public static void string_set_a(int n, char[] s) {
        int i;

        for (i = 0; i < n; ++i) {
            s[i] = 'a';
        }
        s[n] = '\0';
    }
}
```

## 说明

这是一道最简单的字符串构造题：

- 单层循环
- 原地写字符
- 循环后单独补 `'\0'`
