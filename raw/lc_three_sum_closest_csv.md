# LC 3Sum Closest CSV

## Problem

Return the sum of three integers in `nums` closest to `target`.

## Requirements

- `nums` contains at least three integers.
- There is exactly one closest answer in supplied tests.

## Source

- Source: LeetCode problem `3sum-closest`.
- URL: https://leetcode.com/problems/3sum-closest/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_three_sum_closest_csv(const char *nums, int target) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }
    int best = a[0] + a[1] + a[2];
    for (int x = 0; x < n - 2; x++) { int l = x + 1, r = n - 1; while (l < r) { int sum = a[x] + a[l] + a[r]; int d1 = sum - target; if (d1 < 0) d1 = -d1; int d2 = best - target; if (d2 < 0) d2 = -d2; if (d1 < d2) best = sum; if (sum < target) l++; else r--; } }
    return best;
}
```
