# move_zeroes_csv

## Problem

Move all zeroes in comma-separated integer array `nums` to the end while preserving nonzero order.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Preserve relative order of nonzero values.
- Return the transformed array encoding.

## Source

- Source: LeetCode problem `move-zeroes`.
- URL: https://leetcode.com/problems/move-zeroes/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn move_zeroes_csv(nums: &str) -> String {
    if nums.is_empty() { return String::new(); }
    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut out: Vec<String> = Vec::new(); let mut zeros = 0;
    for v in values { if v == 0 { zeros += 1; } else { out.push(v.to_string()); } }
    for _ in 0..zeros { out.push("0".to_string()); }
    out.join(",")
}
```
