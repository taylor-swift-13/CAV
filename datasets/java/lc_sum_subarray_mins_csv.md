# LC Sum Of Subarray Minimums CSV

## Problem

Return the sum of the minimum value of every contiguous subarray.

## Requirements

- `arr` is a comma-separated list of positive integers.
- The supplied sums fit in signed 32-bit range.

## Source

- Source: LeetCode problem `sum-of-subarray-minimums`.
- URL: https://leetcode.com/problems/sum-of-subarray-minimums/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcSumSubarrayMinsCsv {
    public static int lc_sum_subarray_mins_csv(String arr) {
        String[] p = arr.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int sum = 0; for (int l = 0; l < a.length; l++) { int mn = a[l]; for (int r = l; r < a.length; r++) { mn = Math.min(mn, a[r]); sum += mn; } } return sum;
    }
}
```
