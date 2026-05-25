# formal_count_positive_csv

## Problem

Return how many values in comma-separated integer array `nums` are strictly positive.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Zero is not positive.
- Return the count of strictly positive values.

## Source

- Source: FormalBench-inspired program `count-positive`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn formal_count_positive_csv(nums: &str) -> i32 {
    if nums.is_empty() { return 0; }
    nums.split(',').filter(|x| x.parse::<i32>().unwrap() > 0).count() as i32
}
```
