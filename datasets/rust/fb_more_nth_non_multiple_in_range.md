# fb_more_nth_non_multiple_in_range

## Problem

Return the `n`th integer in `[l, r]` that is not divisible by `a`, or `-1` if fewer than `n` such integers exist.

## Requirements

- `1 <= a <= 1000`.
- `1 <= n <= 1000`.
- `0 <= l <= r <= 10000`.

## Source

- Source: FormalBenchHF base program `CountNo.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_more_nth_non_multiple_in_range(a: i32, n: i32, l: i32, r: i32) -> i32 {
    let mut count = 0;
    for i in l..=r { if i % a != 0 { count += 1; } if count == n { return i; } }
    -1
}
```
