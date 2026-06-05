# LC Split Array Largest Sum CSV

## Problem

Split `nums` into `m` nonempty contiguous parts and minimize the largest part sum.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `split-array-largest-sum`.
- URL: https://leetcode.com/problems/split-array-largest-sum/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_split_array_largest_sum_csv(const char *nums, int m) {
    int a[512], n = 0, i = 0, lo = 0, hi = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n++] = v; if (v > lo) lo = v; hi += v; if (nums[i] == ',') i++; } while (lo < hi) { int mid = lo + (hi - lo) / 2, parts = 1, sum = 0; for (int x = 0; x < n; x++) { if (sum + a[x] > mid) { parts++; sum = 0; } sum += a[x]; } if (parts <= m) hi = mid; else lo = mid + 1; } return lo;
}
```
