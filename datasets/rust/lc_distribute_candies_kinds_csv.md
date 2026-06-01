# LC Distribute Candies Kinds CSV

## Problem

Return the maximum number of candy kinds the sister can receive.

## Requirements

- `types` is a comma-separated list of integer candy types.
- The sister receives exactly half of the candies.

## Source

- Source: LeetCode problem `distribute-candies`.
- URL: https://leetcode.com/problems/distribute-candies/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_distribute_candies_kinds_csv(types: &str) -> i32 {
    let a: Vec<i32> = types.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut distinct = 0; let mut i = 0usize; while i < a.len() { let mut seen = false; let mut j = 0usize; while j < i { if a[j] == a[i] { seen = true; } j += 1; } if !seen { distinct += 1; } i += 1; } let half = (a.len() / 2) as i32; if distinct < half { distinct } else { half }
}
```
