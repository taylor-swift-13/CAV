# LC Last Stone Weight II CSV

## Problem

Return the smallest possible final stone weight.

## Requirements

- `stones` is a comma-separated list of positive weights.

## Source

- Source: LeetCode problem `last-stone-weight-ii`.
- URL: https://leetcode.com/problems/last-stone-weight-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_last_stone_weight_ii_csv(const char *stones) {
    int a[256], n = 0, sum = 0, i = 0; while (stones[i] != '\0') { int v = 0; while (stones[i] >= '0' && stones[i] <= '9') { v = v * 10 + stones[i] - '0'; i++; } a[n++] = v; sum += v; if (stones[i] == ',') i++; } int dp[3001] = {0}; for (int x = 0; x < n; x++) for (int s = sum / 2; s >= a[x]; s--) if (dp[s - a[x]] + a[x] > dp[s]) dp[s] = dp[s - a[x]] + a[x]; return sum - 2 * dp[sum / 2];
}
```
