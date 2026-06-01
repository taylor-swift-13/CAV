# LC Range Sum Query CSV

## Problem

Return the sum of comma-separated `nums[left..right]` inclusive.

## Requirements

- `nums` is nonempty.
- `0 <= left <= right < len(nums)`.

## Source

- Source: LeetCode problem `range-sum-query-immutable`.
- URL: https://leetcode.com/problems/range-sum-query-immutable/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcRangeSumQueryCsv {
    public static int lc_range_sum_query_csv(String nums, int left, int right) {
        String[] p = nums.split(","); int sum = 0; for (int i = left; i <= right; i++) sum += Integer.parseInt(p[i]); return sum;
    }
}
```
