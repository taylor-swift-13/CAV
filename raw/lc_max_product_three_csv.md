# LC Maximum Product Of Three Numbers CSV

## Problem

Return the maximum product of any three integers in comma-separated `nums`.

## Requirements

- `nums` contains at least three integers.
- The result fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `maximum-product-of-three-numbers`.
- URL: https://leetcode.com/problems/maximum-product-of-three-numbers/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_max_product_three_csv(const char *nums) {
    int max1 = -2147483647, max2 = -2147483647, max3 = -2147483647, min1 = 2147483647, min2 = 2147483647, i = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (v > max1) { max3 = max2; max2 = max1; max1 = v; } else if (v > max2) { max3 = max2; max2 = v; } else if (v > max3) max3 = v; if (v < min1) { min2 = min1; min1 = v; } else if (v < min2) min2 = v; if (nums[i] == ',') i++; }
    int a = max1 * max2 * max3, b = max1 * min1 * min2; return a > b ? a : b;
}
```
