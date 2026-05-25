# fb_easy_max_mod_remainder_value

## Problem

Return the largest integer `i` in `[1, n]` such that `i % x == y`, or `0` if no such value exists.

## Requirements

- `1 <= n <= 10000`.
- `1 <= x <= 1000`.
- `0 <= y < x`.

## Source

- Source: FormalBenchHF base program `FindMaxVal.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_max_mod_remainder_value(n: i32, x: i32, y: i32) -> i32 {
    let mut max = 0;
    for i in 1..=n { if i % x == y { max = i; } }
    max
}
```
