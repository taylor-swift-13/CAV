# LC Minimum Size Subarray Sum Length CSV

## Problem

Return the minimum length of a contiguous subarray with sum at least `target`, or `0` if none exists.

## Requirements

- `nums` is a nonempty comma-separated list of positive integers.
- `target > 0`.

## Source

- Source: LeetCode problem `minimum-size-subarray-sum`.
- URL: https://leetcode.com/problems/minimum-size-subarray-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_min_subarray_len_csv(int target, const char *nums) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n++] = v; if (nums[i] == ',') i++; }
    int left = 0, sum = 0, best = 1000000; for (int right = 0; right < n; right++) { sum += a[right]; while (sum >= target) { int len = right - left + 1; if (len < best) best = len; sum -= a[left++]; } }
    return best == 1000000 ? 0 : best;
}
```
