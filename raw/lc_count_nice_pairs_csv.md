# LC Count Nice Pairs CSV

## Problem

Return the number of nice pairs where `nums[i] + rev(nums[j]) == nums[j] + rev(nums[i])`.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `count-nice-pairs-in-an-array`.
- URL: https://leetcode.com/problems/count-nice-pairs-in-an-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
static int lc_rev_int(int x) { int r = 0; while (x > 0) { r = r * 10 + x % 10; x /= 10; } return r; }
int lc_count_nice_pairs_csv(const char *nums) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = v - lc_rev_int(v); n++; if (nums[i] == ',') i++; } int ans = 0; for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[x] == a[y]) ans++; return ans;
}
```
