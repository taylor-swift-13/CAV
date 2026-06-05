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

```c
int lc_max_subarray_sum_csv(const char *nums) {
    int best = -2147483647, cur = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (cur < 0) cur = v; else cur += v; if (cur > best) best = cur; if (nums[i] == ',') i++; }
    return best;
}
```
