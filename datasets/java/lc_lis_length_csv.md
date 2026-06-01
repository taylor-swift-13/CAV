# LC Longest Increasing Subsequence Length CSV

## Problem

Return the length of the longest strictly increasing subsequence in comma-separated integers.

## Requirements

- `nums` is nonempty.
- The answer fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `longest-increasing-subsequence`.
- URL: https://leetcode.com/problems/longest-increasing-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLisLengthCsv {
    public static int lc_lis_length_csv(String nums) {
        String[] p = nums.split(","); int n = p.length; int[] a = new int[n]; for (int i = 0; i < n; i++) a[i] = Integer.parseInt(p[i]);
        int[] dp = new int[n]; int best = 1; for (int i = 0; i < n; i++) { dp[i] = 1; for (int j = 0; j < i; j++) if (a[j] < a[i] && dp[j] + 1 > dp[i]) dp[i] = dp[j] + 1; if (dp[i] > best) best = dp[i]; }
        return best;
    }
}
```
