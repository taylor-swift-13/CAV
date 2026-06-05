# LC Product Except Self Sum CSV

## Problem

Compute product-except-self for each comma-separated integer and return the sum of the output array.

## Requirements

- `nums` is nonempty.
- No division is used.
- Intermediate products fit in signed 32-bit integer range.

## Source

- Source: LeetCode problem `product-of-array-except-self`.
- URL: https://leetcode.com/problems/product-of-array-except-self/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_product_except_self_sum_csv(const char *nums) {
    int a[128], n = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = sign * v; n++; if (nums[i] == ',') i++; }
    int left[128], right[128]; left[0] = 1; for (int j = 1; j < n; j++) left[j] = left[j - 1] * a[j - 1]; right[n - 1] = 1; for (int j = n - 2; j >= 0; j--) right[j] = right[j + 1] * a[j + 1];
    int sum = 0; for (int j = 0; j < n; j++) sum += left[j] * right[j];
    return sum;
}
```
