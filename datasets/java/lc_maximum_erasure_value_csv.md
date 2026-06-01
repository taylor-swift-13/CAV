# LC Maximum Erasure Value CSV

## Problem

Return the maximum sum of a subarray with all distinct elements.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `maximum-erasure-value`.
- URL: https://leetcode.com/problems/maximum-erasure-value/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMaximumErasureValueCsv {
    public static int lc_maximum_erasure_value_csv(String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int best = 0; for (int l = 0; l < a.length; l++) { int sum = 0; boolean ok = true; for (int r = l; r < a.length && ok; r++) { for (int t = l; t < r; t++) if (a[t] == a[r]) ok = false; if (ok) { sum += a[r]; best = Math.max(best, sum); } } } return best;
    }
}
```
