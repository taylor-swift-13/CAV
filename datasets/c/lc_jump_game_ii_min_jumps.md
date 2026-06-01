# LC Jump Game II Min Jumps

## Problem

Return the minimum number of jumps needed to reach the last index.

## Requirements

- `nums` is a comma-separated list of nonnegative jump lengths.
- The last index is reachable.

## Source

- Source: LeetCode problem `jump-game-ii`.
- URL: https://leetcode.com/problems/jump-game-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_jump_game_ii_min_jumps(const char *nums) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; } int jumps = 0, end = 0, far = 0; for (int idx = 0; idx < n - 1; idx++) { if (idx + a[idx] > far) far = idx + a[idx]; if (idx == end) { jumps++; end = far; } } return jumps;
}
```
