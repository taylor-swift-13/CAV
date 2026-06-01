# LC Best Sightseeing Pair Score CSV

## Problem

Return the maximum score `values[i] + values[j] + i - j` for `i < j`.

## Requirements

- `values` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `best-sightseeing-pair`.
- URL: https://leetcode.com/problems/best-sightseeing-pair/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_best_sightseeing_pair_score_csv(values: &str) -> i32 {
    let a: Vec<i32> = values.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut best_left = a[0]; let mut ans = i32::MIN; let mut j = 1usize; while j < a.len() { ans = ans.max(best_left + a[j] - j as i32); best_left = best_left.max(a[j] + j as i32); j += 1; } ans
}
```
