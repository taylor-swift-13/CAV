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

```java
class LcProductExceptSelfSumCsv {
    public static int lc_product_except_self_sum_csv(String nums) {
        String[] parts = nums.split(","); int n = parts.length; int[] a = new int[n];
        for (int i = 0; i < n; i++) a[i] = Integer.parseInt(parts[i]);
        int[] left = new int[n], right = new int[n]; left[0] = 1; for (int i = 1; i < n; i++) left[i] = left[i - 1] * a[i - 1]; right[n - 1] = 1; for (int i = n - 2; i >= 0; i--) right[i] = right[i + 1] * a[i + 1];
        int sum = 0; for (int i = 0; i < n; i++) sum += left[i] * right[i];
        return sum;
    }
}
```
