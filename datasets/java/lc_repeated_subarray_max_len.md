# LC Maximum Length Of Repeated Subarray

## Problem

Return the maximum length of a subarray appearing in both arrays.

## Requirements

- Arrays are comma-separated integer lists.

## Source

- Source: LeetCode problem `maximum-length-of-repeated-subarray`.
- URL: https://leetcode.com/problems/maximum-length-of-repeated-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcRepeatedSubarrayMaxLen {
    public static int lc_repeated_subarray_max_len(String nums1, String nums2) {
        String[] p = nums1.split(","), q = nums2.split(","); int[][] dp = new int[p.length + 1][q.length + 1]; int best = 0; for (int i = 1; i <= p.length; i++) for (int j = 1; j <= q.length; j++) if (p[i - 1].equals(q[j - 1])) { dp[i][j] = dp[i - 1][j - 1] + 1; best = Math.max(best, dp[i][j]); } return best;
    }
}
```
