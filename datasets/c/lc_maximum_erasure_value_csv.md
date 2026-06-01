# LC Maximum Erasure Value CSV

## Problem

Return the maximum sum of a subarray with all distinct elements.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `maximum-erasure-value`.
- URL: https://leetcode.com/problems/maximum-erasure-value/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_maximum_erasure_value_csv(const char *nums) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; } int best = 0; for (int l = 0; l < n; l++) { int sum = 0, ok = 1; for (int r = l; r < n && ok; r++) { for (int t = l; t < r; t++) if (a[t] == a[r]) ok = 0; if (ok) { sum += a[r]; if (sum > best) best = sum; } } } return best;
}
```
