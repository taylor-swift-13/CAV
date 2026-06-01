# LC 3Sum Closest CSV

## Problem

Return the sum of three integers in `nums` closest to `target`.

## Requirements

- `nums` contains at least three integers.
- There is exactly one closest answer in supplied tests.

## Source

- Source: LeetCode problem `3sum-closest`.
- URL: https://leetcode.com/problems/3sum-closest/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcThreeSumClosestCsv {
    public static int lc_three_sum_closest_csv(String nums, int target) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); int best = a[0] + a[1] + a[2];
        for (int i = 0; i < a.length - 2; i++) { int l = i + 1, r = a.length - 1; while (l < r) { int sum = a[i] + a[l] + a[r]; if (Math.abs(sum - target) < Math.abs(best - target)) best = sum; if (sum < target) l++; else r--; } } return best;
    }
}
```
