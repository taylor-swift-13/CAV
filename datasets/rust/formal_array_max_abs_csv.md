# formal_array_max_abs_csv

## Problem

Return the largest absolute value in nonempty comma-separated integer array `nums`.

## Requirements

- `nums` is nonempty and comma-separated.
- Negative values are allowed.
- Return the maximum absolute value.
- The absolute values fit in signed 32-bit integer range.

## Source

- Source: FormalBench-inspired program `array-max-abs`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn formal_array_max_abs_csv(nums: &str) -> i32 {
    nums.split(',').map(|x| { let mut v = x.parse::<i32>().unwrap(); if v < 0 { v = -v; } v }).max().unwrap()
}
```
