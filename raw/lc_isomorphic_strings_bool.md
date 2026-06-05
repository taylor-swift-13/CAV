# LC Isomorphic Strings Bool

## Problem

Return true if two ASCII strings are isomorphic.

## Requirements

- Both strings have the same length.
- A bijection between characters must preserve order.

## Source

- Source: LeetCode problem `isomorphic-strings`.
- URL: https://leetcode.com/problems/isomorphic-strings/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_isomorphic_strings_bool(const char *s, const char *t) {
    int st[256] = {0}, ts[256] = {0};
    for (int i = 0; s[i] != '\0'; i++) { unsigned char a = (unsigned char)s[i], b = (unsigned char)t[i]; if (st[a] != ts[b]) return 0; st[a] = i + 1; ts[b] = i + 1; }
    return 1;
}
```
