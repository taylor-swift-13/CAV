# LC Continuous Subarray Sum Bool CSV

## Problem

Return true if a length-at-least-two contiguous subarray has sum divisible by `k`.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.
- `k > 0`.

## Source

- Source: LeetCode problem `continuous-subarray-sum`.
- URL: https://leetcode.com/problems/continuous-subarray-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcContinuousSubarraySumBoolCsv {
    public static boolean lc_continuous_subarray_sum_bool_csv(String nums, int k) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); for (int l = 0; l < a.length; l++) { int sum = 0; for (int r = l; r < a.length; r++) { sum += a[r]; if (r > l && sum % k == 0) return true; } } return false;
    }
}
```
