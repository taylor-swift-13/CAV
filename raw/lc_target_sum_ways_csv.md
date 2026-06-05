# LC Target Sum Ways CSV

## Problem

Return how many sign assignments make comma-separated nonnegative integers sum to `target`.

## Requirements

- `nums` contains nonnegative integers.
- The transformed subset sum fits the fixed DP capacity used by the tests.

## Source

- Source: LeetCode problem `target-sum`.
- URL: https://leetcode.com/problems/target-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_target_sum_ways_csv(const char *nums, int target) {
    int a[128], n = 0, total = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; total += v; if (nums[i] == ',') i++; }
    int want = total + target; if (want < 0 || want % 2 != 0) return 0; want /= 2; int dp[2001] = {0}; dp[0] = 1;
    for (int j = 0; j < n; j++) for (int s = want; s >= a[j]; s--) dp[s] += dp[s - a[j]];
    return dp[want];
}
```
