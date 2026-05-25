# count_good_pairs_csv

## Problem

Return the number of index pairs `(i,j)` with `i < j` and equal values in comma-separated integer array `nums`.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Count pairs of distinct indices with equal values.
- Return the pair count, not the values.

## Source

- Source: LeetCode problem `number-of-good-pairs`.
- URL: https://leetcode.com/problems/number-of-good-pairs/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn count_good_pairs_csv(nums: &str) -> i32 {
    if nums.is_empty() { return 0; }
    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut count = 0;
    for i in 0..values.len() { for j in i + 1..values.len() { if values[i] == values[j] { count += 1; } } }
    count
}
```
