# LC Tuple With Same Product Count CSV

## Problem

Return how many ordered tuples have equal pair products.

## Requirements

- `nums` is a comma-separated list of distinct positive integers.

## Source

- Source: LeetCode problem `tuple-with-same-product`.
- URL: https://leetcode.com/problems/tuple-with-same-product/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_tuple_same_product_count_csv(const char *nums) {
    int a[256], prod[32768], pn = 0, n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = v; n++; if (nums[i] == ',') i++; } for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) { prod[pn] = a[x] * a[y]; pn++; } int ans = 0; for (int x = 0; x < pn; x++) for (int y = x + 1; y < pn; y++) if (prod[x] == prod[y]) ans += 8; return ans;
}
```
