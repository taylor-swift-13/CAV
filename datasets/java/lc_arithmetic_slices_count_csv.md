# LC Arithmetic Slices Count CSV

## Problem

Return how many contiguous arithmetic subarrays of length at least 3 exist.

## Requirements

- `nums` is a nonempty comma-separated list of integers.

## Source

- Source: LeetCode problem `arithmetic-slices`.
- URL: https://leetcode.com/problems/arithmetic-slices/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcArithmeticSlicesCountCsv {
    public static int lc_arithmetic_slices_count_csv(String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int cur = 0, ans = 0; for (int i = 2; i < a.length; i++) { if (a[i] - a[i - 1] == a[i - 1] - a[i - 2]) cur++; else cur = 0; ans += cur; } return ans;
    }
}
```
