# LC Arithmetic Slices Count CSV

## Problem

Return how many contiguous arithmetic subarrays of length at least 3 exist.

## Requirements

- `nums` is a nonempty comma-separated list of integers.

## Source

- Source: LeetCode problem `arithmetic-slices`.
- URL: https://leetcode.com/problems/arithmetic-slices/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_arithmetic_slices_count_csv(const char *nums) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }
    int cur = 0, ans = 0; for (int j = 2; j < n; j++) { if (a[j] - a[j - 1] == a[j - 1] - a[j - 2]) cur++; else cur = 0; ans += cur; } return ans;
}
```
