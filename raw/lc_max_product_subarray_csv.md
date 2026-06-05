# LC Maximum Product Subarray CSV

## Problem

Return the maximum product of a nonempty contiguous subarray.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `maximum-product-subarray`.
- URL: https://leetcode.com/problems/maximum-product-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_max_product_subarray_csv(const char *nums) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = sign * v; n++; if (nums[i] == ',') i++; }
    int maxp = a[0], minp = a[0], best = a[0]; for (int j = 1; j < n; j++) { int x = a[j]; if (x < 0) { int t = maxp; maxp = minp; minp = t; } maxp = x > maxp * x ? x : maxp * x; minp = x < minp * x ? x : minp * x; if (maxp > best) best = maxp; } return best;
}
```
