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

```java
class LcMaxProductSubarrayCsv {
    public static int lc_max_product_subarray_csv(String nums) {
        String[] p = nums.split(","); int maxp = Integer.parseInt(p[0]), minp = maxp, best = maxp; for (int i = 1; i < p.length; i++) { int x = Integer.parseInt(p[i]); if (x < 0) { int t = maxp; maxp = minp; minp = t; } maxp = Math.max(x, maxp * x); minp = Math.min(x, minp * x); best = Math.max(best, maxp); } return best;
    }
}
```
