# LC Longest Common Subsequence Length

## Problem

Return the length of the longest common subsequence of two ASCII strings.

## Requirements

- String lengths are at most `63`.
- Subsequence characters keep relative order but need not be contiguous.

## Source

- Source: LeetCode problem `longest-common-subsequence`.
- URL: https://leetcode.com/problems/longest-common-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLcsLength {
    public static int lc_lcs_length(String text1, String text2) {
        int n = text1.length(), m = text2.length();
        int[][] dp = new int[n + 1][m + 1];
        for (int i = 1; i <= n; i++) for (int j = 1; j <= m; j++) {
            if (text1.charAt(i - 1) == text2.charAt(j - 1)) dp[i][j] = dp[i - 1][j - 1] + 1;
            else dp[i][j] = dp[i - 1][j] > dp[i][j - 1] ? dp[i - 1][j] : dp[i][j - 1];
        }
        return dp[n][m];
    }
}
```
