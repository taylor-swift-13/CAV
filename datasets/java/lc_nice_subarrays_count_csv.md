# LC Count Number Of Nice Subarrays CSV

## Problem

Return how many contiguous subarrays contain exactly `k` odd numbers.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `count-number-of-nice-subarrays`.
- URL: https://leetcode.com/problems/count-number-of-nice-subarrays/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcNiceSubarraysCountCsv {
    public static int lc_nice_subarrays_count_csv(String nums, int k) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int ans = 0; for (int l = 0; l < a.length; l++) { int odds = 0; for (int r = l; r < a.length; r++) { if (a[r] % 2 == 1) odds++; if (odds == k) ans++; } } return ans;
    }
}
```
