# sign_of_product_csv

## Problem

Return the sign of the product of comma-separated integers: `1`, `-1`, or `0`.

## Requirements

- The empty string is treated as an empty product with sign `1`.
- Return `0` if any value is zero.
- Return `-1` for an odd number of negative nonzero values.
- Return `1` otherwise.

## Source

- Source: LeetCode problem `sign-of-the-product-of-an-array`.
- URL: https://leetcode.com/problems/sign-of-the-product-of-an-array/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sign_of_product_csv(const char *nums) {
    int sign = 1;
    int i = 0;
    while (nums[i] != '\0') {
        int neg = 0;
        if (nums[i] == '-') { neg = 1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        if (v == 0) return 0;
        if (neg) sign = -sign;
        if (nums[i] == ',') i++;
    }
    return sign;
}
```
