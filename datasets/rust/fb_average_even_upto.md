# fb_average_even_upto

## Problem

Return the integer average of all positive even integers from `1` through `n`.

## Requirements

- `2 <= n <= 10000`.
- Use truncating integer division.

## Source

- Source: FormalBenchHF base program `AverageEven.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_average_even_upto(n: i32) -> i32 {
    let (mut sum, mut count) = (0, 0);
    for i in 1..=n { if i % 2 == 0 { sum += i; count += 1; } }
    sum / count
}
```
