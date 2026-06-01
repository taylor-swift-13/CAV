# LC Count Good Meals CSV

## Problem

Return the number of pairs whose sum is a power of two.

## Requirements

- `deliciousness` is a comma-separated list of nonnegative integers.
- The supplied counts fit in signed 32-bit range.

## Source

- Source: LeetCode problem `count-good-meals`.
- URL: https://leetcode.com/problems/count-good-meals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_count_good_meals_csv(deliciousness: &str) -> i32 {
    let a: Vec<i32> = deliciousness.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut ans = 0; let mut i = 0usize; while i < a.len() { let mut j = i + 1; while j < a.len() { let s = a[i] + a[j]; if s > 0 && (s & (s - 1)) == 0 { ans += 1; } j += 1; } i += 1; } ans
}
```
