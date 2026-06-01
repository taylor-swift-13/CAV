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

```java
class LcCombinationSum4CountCsv {
    public static int lc_combination_sum4_count_csv(String nums, int target) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int[] dp = new int[target + 1]; dp[0] = 1;
        for (int s = 1; s <= target; s++) for (int v : a) if (s >= v) dp[s] += dp[s - v]; return dp[target];
    }
}
```
