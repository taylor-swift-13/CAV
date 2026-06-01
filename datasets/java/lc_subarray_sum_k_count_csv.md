# LC Subarray Sum Equals K Count CSV

## Problem

Return how many contiguous subarrays of comma-separated `nums` sum to `k`.

## Requirements

- The empty string represents an empty array.
- The count fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `subarray-sum-equals-k`.
- URL: https://leetcode.com/problems/subarray-sum-equals-k/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcSubarraySumKCountCsv {
    public static int lc_subarray_sum_k_count_csv(String nums, int k) {
        if (nums.isEmpty()) return 0;
        String[] parts = nums.split(",");
        int[] a = new int[parts.length];
        for (int i = 0; i < parts.length; i++) a[i] = Integer.parseInt(parts[i]);
        int count = 0;
        for (int l = 0; l < a.length; l++) { int sum = 0; for (int r = l; r < a.length; r++) { sum += a[r]; if (sum == k) count++; } }
        return count;
    }
}
```
