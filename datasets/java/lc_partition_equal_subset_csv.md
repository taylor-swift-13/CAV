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

```java
class LcPartitionEqualSubsetCsv {
    public static boolean lc_partition_equal_subset_csv(String nums) {
        if (nums.isEmpty()) return false;
        String[] parts = nums.split(","); int[] a = new int[parts.length]; int sum = 0;
        for (int i = 0; i < parts.length; i++) { a[i] = Integer.parseInt(parts[i]); sum += a[i]; }
        if (sum % 2 != 0) return false;
        int target = sum / 2; boolean[] dp = new boolean[target + 1]; dp[0] = true;
        for (int v : a) for (int s = target; s >= v; s--) if (dp[s - v]) dp[s] = true;
        return dp[target];
    }
}
```
