# fb_search_big_difference

## Problem

Return the difference between the maximum and minimum value in the first `n` elements of `nums`.

## Requirements

- `1 <= n <= nums.length <= 50`.
- Values are signed 32-bit integers.

## Source

- Source: FormalBenchHF base program `BigDiff.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_big_difference(nums: &[i32], n: i32) -> i32 {
    let (mut max, mut min) = (nums[0], nums[0]);
    for i in 1..(n as usize) { if nums[i] > max { max = nums[i]; } if nums[i] < min { min = nums[i]; } }
    max - min
}
```
