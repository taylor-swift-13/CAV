# fb_search_missing_sequence_value

## Problem

Given the first `n` values of a sequence expected to contain `1,2,...`, return the first missing position found by the FormalBench scan.

## Requirements

- `0 <= n <= ar.length <= 50`.
- The array is intended to start at `1`.

## Source

- Source: FormalBenchHF base program `FindMissing.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_missing_sequence_value(ar: &[i32], n: i32) -> i32 {
    let mut missing = 1; if n == 0 || n == 1 { return missing; }
    for i in 1..=n { if ar[i as usize - 1] == i { missing = i; } else { return i; } }
    missing
}
```
