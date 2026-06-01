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

```java
class LcTargetSumWaysCsv {
    public static int lc_target_sum_ways_csv(String nums, int target) {
        String[] p = nums.split(","); int[] a = new int[p.length]; int total = 0; for (int i = 0; i < p.length; i++) { a[i] = Integer.parseInt(p[i]); total += a[i]; }
        int want = total + target; if (want < 0 || want % 2 != 0) return 0; want /= 2; int[] dp = new int[want + 1]; dp[0] = 1; for (int v : a) for (int s = want; s >= v; s--) dp[s] += dp[s - v]; return dp[want];
    }
}
```
