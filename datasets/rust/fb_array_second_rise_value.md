# fb_array_second_rise_value

## Problem

Return the FormalBench scan value that tracks the previous minimum before a later larger value.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `GetGcd.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_second_rise_value(arr: &[i32], n: i32) -> i32 {
    let (mut result, mut min) = (0, arr[0]);
    for i in 1..(n as usize) { let x = arr[i]; if x > min { if result < min { result = min; } } else { min = x; } }
    result
}
```
