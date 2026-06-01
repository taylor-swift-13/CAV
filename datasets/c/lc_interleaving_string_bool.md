# LC Interleaving String Bool

## Problem

Return true if `s3` is an interleaving of `s1` and `s2`.

## Requirements

- Character order from each source string must be preserved.

## Source

- Source: LeetCode problem `interleaving-string`.
- URL: https://leetcode.com/problems/interleaving-string/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_interleaving_string_bool(const char *s1, const char *s2, const char *s3) {
    int n = 0, m = 0, z = 0; while (s1[n] != '\0') n++; while (s2[m] != '\0') m++; while (s3[z] != '\0') z++; if (n + m != z) return 0; int dp[128][128] = {{0}}; dp[0][0] = 1; for (int i = 0; i <= n; i++) for (int j = 0; j <= m; j++) { if (i > 0 && dp[i - 1][j] && s1[i - 1] == s3[i + j - 1]) dp[i][j] = 1; if (j > 0 && dp[i][j - 1] && s2[j - 1] == s3[i + j - 1]) dp[i][j] = 1; } return dp[n][m];
}
```
