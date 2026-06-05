# LC Combination Sum IV Count CSV

## Problem

Return the number of ordered combinations from `nums` that sum to `target`.

## Requirements

- `nums` is a nonempty comma-separated list of positive distinct integers.
- `target >= 0`.
- The count fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `combination-sum-iv`.
- URL: https://leetcode.com/problems/combination-sum-iv/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_combination_sum4_count_csv(const char *nums, int target) {
    int a[128], n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = v; n++; if (nums[i] == ',') i++; }
    int dp[1001] = {0}; dp[0] = 1; for (int s = 1; s <= target; s++) for (int j = 0; j < n; j++) if (s >= a[j]) dp[s] += dp[s - a[j]];
    return dp[target];
}
```
