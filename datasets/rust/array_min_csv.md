# array_min_csv

## Problem

Return the minimum value in nonempty comma-separated integer string `nums`.

## Requirements

- `nums` is nonempty and comma-separated with no spaces.
- Return the smallest integer value.
- Negative numbers are allowed.
- At most 64 integers are encoded.

## Source

- Source: FormalBench-inspired program `array-min`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn array_min_csv(nums: &str) -> i32 {
    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut best = values[0];
    for v in values { if v < best { best = v; } }
    best
}
```
