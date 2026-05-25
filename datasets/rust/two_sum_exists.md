# two_sum_exists

## Problem

Return true if two distinct elements in integer array string `nums` sum to `target`.

## Requirements

- `nums` is encoded as comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- A valid pair must use two distinct positions, even if the values are equal.
- Return only whether such a pair exists; do not return indices.
- The number of encoded integers is at most 64 in this dataset variant.

## Source

- Source: LeetCode problem `two-sum`.
- URL: https://leetcode.com/problems/two-sum/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn two_sum_exists(nums: &str, target: i32) -> bool {
    let values: Vec<i32> = if nums.is_empty() { Vec::new() } else { nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };
    let mut i = 0;
    while i < values.len() {
        let mut j = i + 1;
        while j < values.len() {
            if values[i] + values[j] == target { return true; }
            j += 1;
        }
        i += 1;
    }
    false
}
```
