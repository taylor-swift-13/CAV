# LC Continuous Subarray Sum Bool CSV

## Problem

Return true if a length-at-least-two contiguous subarray has sum divisible by `k`.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.
- `k > 0`.

## Source

- Source: LeetCode problem `continuous-subarray-sum`.
- URL: https://leetcode.com/problems/continuous-subarray-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_continuous_subarray_sum_bool_csv(const char *nums, int k) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; }
    for (int l = 0; l < n; l++) { int sum = 0; for (int r = l; r < n; r++) { sum += a[r]; if (r > l && sum % k == 0) return 1; } } return 0;
}
```
