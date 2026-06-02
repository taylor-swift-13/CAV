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

```c
int lc_subarray_sum_k_count_csv(const char *nums, int k) {
    int a[128], n = 0, i = 0;
    if (nums[0] == '\0') return 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }
    int count = 0;
    for (int l = 0; l < n; l++) { int sum = 0; for (int r = l; r < n; r++) { sum += a[r]; if (sum == k) count++; } }
    return count;
}
```
