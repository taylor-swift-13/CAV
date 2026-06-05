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

```java
class LcProfitableSchemesCount {
    public static int lc_profitable_schemes_count(int n, int min_profit, String group, String profit) {
        String[] gs = group.split(","), ps = profit.split(","); int jobs = gs.length, mod = 1000000007; int[] g = new int[jobs], p = new int[jobs]; for (int i = 0; i < jobs; i++) { g[i] = Integer.parseInt(gs[i]); p[i] = Integer.parseInt(ps[i]); } int[][] dp = new int[n + 1][min_profit + 1]; dp[0][0] = 1; for (int job = 0; job < jobs; job++) for (int members = n; members >= g[job]; members--) for (int prof = min_profit; prof >= 0; prof--) { int prev = Math.max(0, prof - p[job]); dp[members][prof] = (dp[members][prof] + dp[members - g[job]][prev]) % mod; } int ans = 0; for (int members = 0; members <= n; members++) ans = (ans + dp[members][min_profit]) % mod; return ans;
    }
}
```
