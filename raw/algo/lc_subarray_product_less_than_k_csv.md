# LC Subarray Product Less Than K CSV

## Problem

Return how many contiguous subarrays have product strictly less than `k`.

## Requirements

- `nums` is a nonempty comma-separated list of positive integers.
- `k >= 0`.

## Source

- Source: LeetCode problem `subarray-product-less-than-k`.
- URL: https://leetcode.com/problems/subarray-product-less-than-k/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_subarray_product_less_than_k_csv(const char *nums, int k) {
    if (k <= 1) return 0;
    int a[256], n = 0, i = 0;
    while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = v; n++; if (nums[i] == ',') i++; }
    int left = 0, prod = 1, ans = 0; for (int right = 0; right < n; right++) { prod *= a[right]; while (prod >= k) prod /= a[left++]; ans += right - left + 1; } return ans;
}
```
