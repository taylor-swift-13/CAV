# LC H Index CSV

## Problem

Return the H-index for comma-separated citation counts.

## Requirements

- `citations` is a nonempty comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `h-index`.
- URL: https://leetcode.com/problems/h-index/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_h_index_csv(citations: &str) -> i32 {
    let mut a: Vec<i32> = citations.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.sort(); let n = a.len(); let mut h = 0; let mut i = 0usize; while i < n { let cand = (n - i) as i32; if a[i] >= cand && cand > h { h = cand; } i += 1; } h
}
```
