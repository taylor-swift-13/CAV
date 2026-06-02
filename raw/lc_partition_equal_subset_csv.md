# LC Partition Equal Subset CSV

## Problem

Return true if comma-separated positive integers can be partitioned into two subsets with equal sum.

## Requirements

- The empty string returns false.
- The total sum is at most `2000`.

## Source

- Source: LeetCode problem `partition-equal-subset-sum`.
- URL: https://leetcode.com/problems/partition-equal-subset-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_partition_equal_subset_csv(const char *nums) {
    if (nums[0] == '\0') return 0;
    int a[128], n = 0, sum = 0, i = 0;
    while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; sum += v; if (nums[i] == ',') i++; }
    if (sum % 2 != 0) return 0;
    int target = sum / 2; int dp[2001] = {0}; dp[0] = 1;
    for (int k = 0; k < n; k++) for (int s = target; s >= a[k]; s--) if (dp[s - a[k]]) dp[s] = 1;
    return dp[target];
}
```
