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

```java
class LcInterleavingStringBool {
    public static boolean lc_interleaving_string_bool(String s1, String s2, String s3) {
        int n = s1.length(), m = s2.length(); if (n + m != s3.length()) return false; boolean[][] dp = new boolean[n + 1][m + 1]; dp[0][0] = true; for (int i = 0; i <= n; i++) for (int j = 0; j <= m; j++) { if (i > 0 && dp[i - 1][j] && s1.charAt(i - 1) == s3.charAt(i + j - 1)) dp[i][j] = true; if (j > 0 && dp[i][j - 1] && s2.charAt(j - 1) == s3.charAt(i + j - 1)) dp[i][j] = true; } return dp[n][m];
    }
}
```
