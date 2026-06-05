# LC Profitable Schemes Count

## Problem

Return how many subsets of jobs use at most `n` members and earn at least `min_profit`.

## Requirements

- `group` and `profit` are comma-separated lists of equal length.
- Return the count modulo `1_000_000_007`.

## Source

- Source: LeetCode problem `profitable-schemes`.
- URL: https://leetcode.com/problems/profitable-schemes/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_profitable_schemes_count(int n, int min_profit, const char *group, const char *profit) {
    int g[128], p[128], jobs = 0, i = 0; while (group[i] != '\0') { int v = 0; while (group[i] >= '0' && group[i] <= '9') { v = v * 10 + group[i] - '0'; i++; } g[jobs++] = v; if (group[i] == ',') i++; } i = 0; int m = 0; while (profit[i] != '\0') { int v = 0; while (profit[i] >= '0' && profit[i] <= '9') { v = v * 10 + profit[i] - '0'; i++; } p[m++] = v; if (profit[i] == ',') i++; } int mod = 1000000007; int dp[101][101] = {{0}}; dp[0][0] = 1; for (int job = 0; job < jobs; job++) for (int members = n; members >= g[job]; members--) for (int prof = min_profit; prof >= 0; prof--) { int prev = prof - p[job]; if (prev < 0) prev = 0; dp[members][prof] = (dp[members][prof] + dp[members - g[job]][prev]) % mod; } int ans = 0; for (int members = 0; members <= n; members++) ans = (ans + dp[members][min_profit]) % mod; return ans;
}
```
