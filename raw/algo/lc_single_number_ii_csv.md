# LC Single Number II CSV

## Problem

Return the element that appears once when every other element appears three times.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `single-number-ii`.
- URL: https://leetcode.com/problems/single-number-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_single_number_ii_csv(const char *nums) {
    int ones = 0, twos = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } v *= sign; ones = (ones ^ v) & ~twos; twos = (twos ^ v) & ~ones; if (nums[i] == ',') i++; } return ones;
}
```
