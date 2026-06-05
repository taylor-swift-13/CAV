# LC Palindrome Partitioning II Min Cut

## Problem

Return the minimum cuts needed so every substring part is a palindrome.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `palindrome-partitioning-ii`.
- URL: https://leetcode.com/problems/palindrome-partitioning-ii/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_pal_partition_min_cut(const char *s) {
    int n = 0; while (s[n] != '\0') n++; int pal[128][128] = {{0}}, cut[128]; for (int i = 0; i < n; i++) cut[i] = i; for (int r = 0; r < n; r++) for (int l = r; l >= 0; l--) if (s[l] == s[r] && (r - l < 2 || pal[l + 1][r - 1])) { pal[l][r] = 1; if (l == 0) cut[r] = 0; else if (cut[l - 1] + 1 < cut[r]) cut[r] = cut[l - 1] + 1; } return cut[n - 1];
}
```
