# LC Find The Difference ASCII

## Problem

Return the ASCII code of the extra character in `t` compared with `s`.

## Requirements

- `t` is formed by shuffling `s` and adding one extra lowercase letter.

## Source

- Source: LeetCode problem `find-the-difference`.
- URL: https://leetcode.com/problems/find-the-difference/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcFindDifferenceAscii {
    public static int lc_find_difference_ascii(String s, String t) {
        int x = 0; for (int i = 0; i < s.length(); i++) x ^= s.charAt(i); for (int i = 0; i < t.length(); i++) x ^= t.charAt(i); return x;
    }
}
```
