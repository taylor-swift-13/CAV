# LC Maximum Circular Subarray Sum CSV

## Problem

Return the maximum nonempty subarray sum in a circular array.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `maximum-sum-circular-subarray`.
- URL: https://leetcode.com/problems/maximum-sum-circular-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMaxSubarrayCircularSumCsv {
    public static int lc_max_subarray_circular_sum_csv(String nums) {
        String[] p = nums.split(","); int first = Integer.parseInt(p[0]); int total = first, maxCur = first, maxSum = first, minCur = first, minSum = first; for (int i = 1; i < p.length; i++) { int x = Integer.parseInt(p[i]); total += x; maxCur = Math.max(x, maxCur + x); maxSum = Math.max(maxSum, maxCur); minCur = Math.min(x, minCur + x); minSum = Math.min(minSum, minCur); } if (maxSum < 0) return maxSum; return Math.max(maxSum, total - minSum);
    }
}
```
