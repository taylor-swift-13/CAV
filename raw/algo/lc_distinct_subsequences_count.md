# LC Distinct Subsequences Count

## Problem

Return how many distinct subsequences of `s` equal `t`.

## Requirements

- Inputs are ASCII.
- The supplied counts fit in signed 32-bit range.

## Source

- Source: LeetCode problem `distinct-subsequences`.
- URL: https://leetcode.com/problems/distinct-subsequences/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_distinct_subsequences_count(const char *s, const char *t) {
    int n = 0, m = 0; while (s[n] != '\0') n++; while (t[m] != '\0') m++; long long dp[128] = {0}; dp[0] = 1; for (int i = 0; i < n; i++) for (int j = m - 1; j >= 0; j--) if (s[i] == t[j]) dp[j + 1] += dp[j]; return (int)dp[m];
}
```
