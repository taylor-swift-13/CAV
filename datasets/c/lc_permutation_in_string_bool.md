# LC Permutation In String Bool

## Problem

Return true if `s2` contains any permutation of `s1` as a substring.

## Requirements

- Both strings contain lowercase English letters.

## Source

- Source: LeetCode problem `permutation-in-string`.
- URL: https://leetcode.com/problems/permutation-in-string/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_permutation_in_string_bool(const char *s1, const char *s2) {
    int n = 0, m = 0; while (s1[n] != '\0') n++; while (s2[m] != '\0') m++; if (n > m) return 0; int need[26] = {0}, win[26] = {0}; for (int i = 0; i < n; i++) { need[s1[i] - 'a']++; win[s2[i] - 'a']++; } for (int i = 0; i <= m - n; i++) { int ok = 1; for (int c = 0; c < 26; c++) if (need[c] != win[c]) ok = 0; if (ok) return 1; if (i + n < m) { win[s2[i] - 'a']--; win[s2[i + n] - 'a']++; } } return 0;
}
```
