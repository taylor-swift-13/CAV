# LC Teemo Attacking Duration CSV

## Problem

Return total poisoned duration from attack times and a fixed duration.

## Requirements

- `times` is a nonempty sorted comma-separated list of attack times.
- `duration > 0`.

## Source

- Source: LeetCode problem `teemo-attacking`.
- URL: https://leetcode.com/problems/teemo-attacking/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_teemo_attacking_duration_csv(times: &str, duration: i32) -> i32 {
    let a: Vec<i32> = times.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut ans = duration; let mut i = 1usize; while i < a.len() { let gap = a[i] - a[i - 1]; ans += if gap < duration { gap } else { duration }; i += 1; } ans
}
```
