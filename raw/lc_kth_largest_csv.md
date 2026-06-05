# LC Kth Largest Element CSV

## Problem

Return the `k`th largest value in comma-separated `nums`.

## Requirements

- `nums` is nonempty.
- `1 <= k <= len(nums)`.

## Source

- Source: LeetCode problem `kth-largest-element-in-an-array`.
- URL: https://leetcode.com/problems/kth-largest-element-in-an-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_kth_largest_csv(const char *nums, int k) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = sign * v; n++; if (nums[i] == ',') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] > a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }
    return a[k - 1];
}
```
