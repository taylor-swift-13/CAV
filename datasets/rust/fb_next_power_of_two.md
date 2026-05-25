# fb_next_power_of_two

## Problem

Return the smallest power of two that is greater than or equal to `n`.

## Requirements

- `0 <= n <= 1000000`.
- Return `1` when `n` is `0`.

## Source

- Source: FormalBenchHF base program `NextPowerOf2.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_next_power_of_two(n: i32) -> i32 {
    if n == 0 { return 1; }
    let mut i = 1;
    while i < n { i <<= 1; }
    i
}
```
