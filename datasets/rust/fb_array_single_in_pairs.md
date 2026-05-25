# fb_array_single_in_pairs

## Problem

Given adjacent equal pairs with one unpaired value, return the unpaired value.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `Search.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_single_in_pairs(arr: &[i32], n: i32) -> i32 {
    let mut i = 0usize;
    while i < n as usize - 1 { if arr[i] == arr[i + 1] { i += 2; } else { return arr[i]; } }
    arr[n as usize - 1]
}
```
