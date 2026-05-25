# fb_smallest_multiple

## Problem

Return the smallest positive integer that is divisible by every integer from `1` through `n`.

## Requirements

- `1 <= n <= 10`.
- Return the answer as a signed 32-bit integer.

## Source

- Source: FormalBenchHF base program `SmallestMultiple.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_smallest_multiple(n: i32) -> i32 {
    if n <= 2 { return n; }
    let mut i = n * 2;
    loop {
        for factor in 1..=n {
            if i % factor != 0 { i += n; break; }
            if factor == n { return i; }
        }
    }
}
```
