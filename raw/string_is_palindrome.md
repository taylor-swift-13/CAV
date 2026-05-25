# String Is Palindrome

## 问题描述

实现一个 Java 静态方法，判断给定长度的字符数组是否是回文。

约定：
- `n` 表示要检查的字符个数，`n >= 0`。
- `s` 表示长度至少为 `n` 的字符数组。
- 只检查前 `n` 个字符，不依赖 `'\0'` 结尾。
- 如果前 `n` 个字符正读和反读相同，返回 `1`，否则返回 `0`。

## Java 要求

- 生成的 Java 类名应为 `StringIsPalindrome`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringIsPalindrome {
    public static int string_is_palindrome(int n, char[] s) {
        int left = 0;
        int right = n - 1;
        while (left < right) {
            if (s[left] != s[right]) {
                return 0;
            }
            left++;
            right--;
        }
        return 1;
    }
}
```

## 说明

这段代码用双指针从两端向中间比较字符。只要出现一对不同字符，就可以确定不是回文。
