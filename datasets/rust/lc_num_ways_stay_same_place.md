# LC Number Of Ways Stay Same Place

## Problem

Return how many ways to be at index 0 after exactly `steps` moves.

## Requirements

- At each move, stay, move left, or move right within array bounds.
- Return the count modulo `1_000_000_007`.

## Source

- Source: LeetCode problem `number-of-ways-to-stay-in-the-same-place-after-some-steps`.
- URL: https://leetcode.com/problems/number-of-ways-to-stay-in-the-same-place-after-some-steps/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_num_ways_stay_same_place(steps: i32, arr_len: i32) -> i32 {
    let modu = 1000000007i32; let max_pos = steps.min(arr_len - 1) as usize; let mut dp = vec![0; max_pos + 1]; dp[0] = 1; let mut s = 0; while s < steps { let mut next = vec![0; max_pos + 1]; let mut i = 0usize; while i <= max_pos { next[i] = (next[i] + dp[i]) % modu; if i > 0 { next[i - 1] = (next[i - 1] + dp[i]) % modu; } if i < max_pos { next[i + 1] = (next[i + 1] + dp[i]) % modu; } i += 1; } dp = next; s += 1; } dp[0]
}
```
