# substring_index_ascii

## Problem

Return the first index of `needle` in `haystack`, or `-1` if absent.

## Requirements

- Inputs are ASCII strings.
- Return a zero-based index.
- If `needle` is empty, return `0`.
- Use direct substring matching semantics.

## Source

- Source: LeetCode problem `find-the-index-of-the-first-occurrence-in-a-string`.
- URL: https://leetcode.com/problems/find-the-index-of-the-first-occurrence-in-a-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int substring_index_ascii(const char *haystack, const char *needle) {
    if (needle[0] == '\0') return 0;
    int n = 0, m = 0;
    while (haystack[n] != '\0') n++;
    while (needle[m] != '\0') m++;
    for (int i = 0; i + m <= n; i++) {
        int ok = 1;
        for (int j = 0; j < m; j++) if (haystack[i + j] != needle[j]) ok = 0;
        if (ok) return i;
    }
    return -1;
}
```
