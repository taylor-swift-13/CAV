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

```java
class LcJumpGameIiMinJumps {
    public static int lc_jump_game_ii_min_jumps(String nums) {
        String[] p = nums.split(","); int jumps = 0, end = 0, far = 0; for (int i = 0; i < p.length - 1; i++) { int v = Integer.parseInt(p[i]); far = Math.max(far, i + v); if (i == end) { jumps++; end = far; } } return jumps;
    }
}
```
