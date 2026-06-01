# LC Minimum Size Subarray Sum Length CSV

## Problem

Return the minimum length of a contiguous subarray with sum at least `target`, or `0` if none exists.

## Requirements

- `nums` is a nonempty comma-separated list of positive integers.
- `target > 0`.

## Source

- Source: LeetCode problem `minimum-size-subarray-sum`.
- URL: https://leetcode.com/problems/minimum-size-subarray-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMinSubarrayLenCsv {
    public static int lc_min_subarray_len_csv(int target, String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int left = 0, sum = 0, best = 1000000;
        for (int right = 0; right < a.length; right++) { sum += a[right]; while (sum >= target) { int len = right - left + 1; if (len < best) best = len; sum -= a[left++]; } } return best == 1000000 ? 0 : best;
    }
}
```
