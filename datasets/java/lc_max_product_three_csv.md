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

```java
class LcMaxProductThreeCsv {
    public static int lc_max_product_three_csv(String nums) {
        String[] p = nums.split(","); int max1 = Integer.MIN_VALUE, max2 = Integer.MIN_VALUE, max3 = Integer.MIN_VALUE, min1 = Integer.MAX_VALUE, min2 = Integer.MAX_VALUE;
        for (String part : p) { int v = Integer.parseInt(part); if (v > max1) { max3 = max2; max2 = max1; max1 = v; } else if (v > max2) { max3 = max2; max2 = v; } else if (v > max3) max3 = v; if (v < min1) { min2 = min1; min1 = v; } else if (v < min2) min2 = v; }
        return Math.max(max1 * max2 * max3, max1 * min1 * min2);
    }
}
```
