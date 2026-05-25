# uppercase_ascii_letter

## Problem

Convert a lowercase ASCII letter to uppercase and return it as a one-character string.

## Requirements

- `letter` has length exactly 1.
- Official-style inputs are lowercase ASCII letters `a` through `z`.
- For robustness in this local variant, a non-lowercase ASCII character would be returned unchanged.
- Return a one-character string; do not return an integer code point.

## Source

- Source: Luogu problem `P5704`.
- URL: https://www.luogu.com.cn/problem/P5704
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class UppercaseAsciiLetter {
    public static String uppercase_ascii_letter(String letter) {
        char c = letter.charAt(0);
        if (c >= 'a' && c <= 'z') c = (char)(c - 'a' + 'A');
        return Character.toString(c);
    }
}
```
