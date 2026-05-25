# formal_array_sum_csv

## Problem

Return the sum of all values in comma-separated integer array `nums`.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Return the arithmetic sum.
- The result fits in a signed 32-bit integer.

## Source

- Source: FormalBench-inspired program `array-sum`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn formal_array_sum_csv(nums: &str) -> i32 {
    if nums.is_empty() { return 0; }
    nums.split(',').map(|x| x.parse::<i32>().unwrap()).sum()
}
```
