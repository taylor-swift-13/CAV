# LC Maximum Subarray Sum CSV

## Problem

Return the maximum sum over all nonempty contiguous subarrays.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `maximum-subarray`.
- URL: https://leetcode.com/problems/maximum-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMaxSubarraySumCsv {
    public static int lc_max_subarray_sum_csv(String nums) {
        int best = Integer.MIN_VALUE, cur = 0; for (String part : nums.split(",")) { int v = Integer.parseInt(part); cur = cur < 0 ? v : cur + v; best = Math.max(best, cur); } return best;
    }
}
```
