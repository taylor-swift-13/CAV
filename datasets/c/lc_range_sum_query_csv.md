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

```c
int lc_range_sum_query_csv(const char *nums, int left, int right) {
    int idx = 0, i = 0, sum = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } if (idx >= left && idx <= right) sum += sign * v; idx++; if (nums[i] == ',') i++; } return sum;
}
```
