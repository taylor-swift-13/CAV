# fb_average_odd_upto

## Problem

Return the integer average of all positive odd integers from `1` through `n`.

## Requirements

- `1 <= n <= 10000`.
- Use truncating integer division.

## Source

- Source: FormalBenchHF base program `AverageOdd.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_average_odd_upto(n: i32) -> i32 {
    let (mut sum, mut count) = (0, 0);
    for i in 1..=n { if i % 2 == 1 { sum += i; count += 1; } }
    sum / count
}
```
