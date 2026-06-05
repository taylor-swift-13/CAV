# LC Increasing Triplet Subsequence Bool CSV

## Problem

Return true if the array contains an increasing subsequence of length three.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `increasing-triplet-subsequence`.
- URL: https://leetcode.com/problems/increasing-triplet-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_increasing_triplet_bool_csv(const char *nums) {
    int first = 2147483647, second = 2147483647, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } v *= sign; if (v <= first) first = v; else if (v <= second) second = v; else return 1; if (nums[i] == ',') i++; } return 0;
}
```
