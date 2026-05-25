# fb_common_divisor_count

## Problem

Return the number of positive common divisors of `x` and `y`.

## Requirements

- `1 <= x, y <= 10000`.
- Count each common divisor once.

## Source

- Source: FormalBenchHF base program `NumCommDiv.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_common_divisor_count(x: i32, y: i32) -> i32 {
    let mut count = 0;
    for i in 1..=x.min(y) { if x % i == 0 && y % i == 0 { count += 1; } }
    count
}
```
