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

```c
int lc_find_difference_ascii(const char *s, const char *t) {
    int x = 0; for (int i = 0; s[i] != '\0'; i++) x ^= s[i]; for (int i = 0; t[i] != '\0'; i++) x ^= t[i]; return x;
}
```
