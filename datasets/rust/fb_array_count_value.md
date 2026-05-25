# fb_array_count_value

## Problem

Return how many of the first `n` elements of `tuplex` are equal to `value`.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `CountTuplex.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_count_value(tuplex: &[i32], n: i32, value: i32) -> i32 {
    let mut count = 0;
    for i in 0..(n as usize) { if tuplex[i] == value { count += 1; } }
    count
}
```
