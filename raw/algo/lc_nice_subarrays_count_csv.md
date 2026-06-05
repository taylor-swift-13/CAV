# LC Count Number Of Nice Subarrays CSV

## Problem

Return how many contiguous subarrays contain exactly `k` odd numbers.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `count-number-of-nice-subarrays`.
- URL: https://leetcode.com/problems/count-number-of-nice-subarrays/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_nice_subarrays_count_csv(const char *nums, int k) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = v; n++; if (nums[i] == ',') i++; } int ans = 0; for (int l = 0; l < n; l++) { int odds = 0; for (int r = l; r < n; r++) { if (a[r] % 2) odds++; if (odds == k) ans++; } } return ans;
}
```
