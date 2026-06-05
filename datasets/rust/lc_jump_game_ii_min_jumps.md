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

```rust
pub fn lc_jump_game_ii_min_jumps(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut jumps = 0; let mut end = 0usize; let mut far = 0usize; let mut i = 0usize; while i + 1 < a.len() { far = far.max(i + a[i] as usize); if i == end { jumps += 1; end = far; } i += 1; } jumps
}
```
