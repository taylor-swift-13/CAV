# LC Rabbits In Forest Minimum CSV

## Problem

Return the minimum number of rabbits consistent with the answers.

## Requirements

- `answers` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `rabbits-in-forest`.
- URL: https://leetcode.com/problems/rabbits-in-forest/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_rabbits_forest_min_csv(answers: &str) -> i32 {
    let a: Vec<i32> = answers.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut total = 0; let mut i = 0usize; while i < a.len() { let mut seen = false; let mut j = 0usize; while j < i { if a[j] == a[i] { seen = true; } j += 1; } if !seen { let mut cnt = 0; for &v in &a { if v == a[i] { cnt += 1; } } let group = a[i] + 1; total += ((cnt + group - 1) / group) * group; } i += 1; } total
}
```
