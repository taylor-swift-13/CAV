# LC Jump Game CSV

## Problem

Return true if the last index is reachable from index `0` in comma-separated jump lengths.

## Requirements

- The empty string represents an empty array and returns false.
- Each value is nonnegative.

## Source

- Source: LeetCode problem `jump-game`.
- URL: https://leetcode.com/problems/jump-game/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_can_jump_csv(const char *nums) {
    int reach = 0, idx = 0, i = 0;
    if (nums[0] == '\0') return 0;
    while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } if (idx > reach) return 0; if (idx + v > reach) reach = idx + v; idx++; if (nums[i] == ',') i++; }
    return 1;
}
```
