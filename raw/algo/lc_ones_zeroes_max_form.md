# LC Ones And Zeroes Max Form

## Problem

Return the largest subset size with at most `m` zeroes and `n` ones.

## Requirements

- Binary strings are separated by semicolons.

## Source

- Source: LeetCode problem `ones-and-zeroes`.
- URL: https://leetcode.com/problems/ones-and-zeroes/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_ones_zeroes_max_form(const char *strs, int m, int n) {
    int dp[101][101] = {{0}}, i = 0; while (strs[i] != '\0') { int z = 0, o = 0; while (strs[i] == '0' || strs[i] == '1') { if (strs[i] == '0') z++; else o++; i++; } for (int a = m; a >= z; a--) for (int b = n; b >= o; b--) if (dp[a - z][b - o] + 1 > dp[a][b]) dp[a][b] = dp[a - z][b - o] + 1; if (strs[i] == ';') i++; } return dp[m][n];
}
```
