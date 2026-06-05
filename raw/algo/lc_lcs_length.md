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

```c
int lc_lcs_length(const char *text1, const char *text2) {
    int n = 0, m = 0;
    while (text1[n] != '\0') n++;
    while (text2[m] != '\0') m++;
    int dp[64][64] = {{0}};
    for (int i = 1; i <= n; i++) for (int j = 1; j <= m; j++) {
        if (text1[i - 1] == text2[j - 1]) dp[i][j] = dp[i - 1][j - 1] + 1;
        else dp[i][j] = dp[i - 1][j] > dp[i][j - 1] ? dp[i - 1][j] : dp[i][j - 1];
    }
    return dp[n][m];
}
```
