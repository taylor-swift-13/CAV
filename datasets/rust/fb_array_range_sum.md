# fb_array_range_sum

## Problem

Return the sum of `nums[m]` through `nums[n]`, inclusive.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `SumRangeList.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_range_sum(nums: &[i32], m: i32, n: i32) -> i32 {
    let mut sum = 0;
    for i in (m as usize)..=(n as usize) { sum += nums[i]; }
    sum
}
```
