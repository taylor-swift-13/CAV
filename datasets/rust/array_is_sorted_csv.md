# array_is_sorted_csv

## Problem

Return true if comma-separated integer string `nums` is sorted in nondecreasing order.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string is considered sorted.
- Duplicates are allowed.
- Return false on the first adjacent decrease.

## Source

- Source: FormalBench-inspired program `array-sorted`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn array_is_sorted_csv(nums: &str) -> bool {
    if nums.is_empty() { return true; }
    let values: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut i = 1usize;
    while i < values.len() { if values[i] < values[i - 1] { return false; } i += 1; }
    true
}
```
