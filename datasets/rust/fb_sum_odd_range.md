# fb_sum_odd_range

## Problem

Return the sum of all odd integers in the inclusive range `[l, r]`.

## Requirements

- `0 <= l <= r <= 10000`.
- Return `0` if the range contains no odd values.

## Source

- Source: FormalBenchHF base program `SumInRange.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_sum_odd_range(l: i32, r: i32) -> i32 {
    let mut sum = 0;
    for i in l..=r { if i % 2 == 1 { sum += i; } }
    sum
}
```
