# LC Binary Subarrays With Sum Count CSV

## Problem

Return how many nonempty contiguous subarrays have sum exactly `goal`.

## Requirements

- `nums` is a comma-separated binary array.

## Source

- Source: LeetCode problem `binary-subarrays-with-sum`.
- URL: https://leetcode.com/problems/binary-subarrays-with-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_binary_subarrays_sum_count_csv(const char *nums, int goal) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { a[n++] = nums[i] - '0'; i++; if (nums[i] == ',') i++; } int ans = 0; for (int l = 0; l < n; l++) { int sum = 0; for (int r = l; r < n; r++) { sum += a[r]; if (sum == goal) ans++; } } return ans;
}
```
