# is_subsequence_ascii

## Problem

Return true if `s` is a subsequence of `t`.

## Requirements

- Inputs are ASCII strings.
- Characters must appear in the same order but need not be adjacent.
- The empty string is a subsequence of every string.
- Return false if `s` still has unmatched characters after scanning `t`.

## Source

- Source: LeetCode problem `is-subsequence`.
- URL: https://leetcode.com/problems/is-subsequence/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int is_subsequence_ascii(const char *s, const char *t) {
    int i = 0;
    int j = 0;
    while (s[i] != '\0' && t[j] != '\0') {
        if (s[i] == t[j]) i++;
        j++;
    }
    return s[i] == '\0';
}
```
