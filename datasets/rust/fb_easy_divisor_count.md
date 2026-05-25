# fb_easy_divisor_count

## Problem

Return the number of positive divisors of `n`.

## Requirements

- `1 <= n <= 10000`.
- Count both `1` and `n`.

## Source

- Source: FormalBenchHF base program `Divisor.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_divisor_count(mut n: i32) -> i32 {
    let mut count = 0;
    for i in 1..=n { if n % i == 0 { count += 1; } }
    count
}
```
