# fb_easy_round_down_multiple

## Problem

Return the largest multiple of `m` that is less than or equal to `n`.

## Requirements

- `0 <= n <= 10000`.
- `1 <= m <= 1000`.

## Source

- Source: FormalBenchHF base program `RoundNum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_round_down_multiple(n: i32, m: i32) -> i32 {
    let mut i = n;
    while i >= 0 { if i % m == 0 { return i; } i -= 1; }
    -1
}
```
