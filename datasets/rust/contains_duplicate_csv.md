# contains_duplicate_csv

## Problem

Return true if comma-separated integer string `nums` contains the same value at least twice.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Return true if any two distinct positions contain equal values.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `contains-duplicate`.
- URL: https://leetcode.com/problems/contains-duplicate/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn contains_duplicate_csv(nums: &str) -> bool {
    if nums.is_empty() { return false; }
    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut i = 0;
    while i < values.len() { let mut j = i + 1; while j < values.len() { if values[i] == values[j] { return true; } j += 1; } i += 1; }
    false
}
```
