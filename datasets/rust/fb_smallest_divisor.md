# fb_smallest_divisor

## Problem

Return the smallest divisor of `n` that is greater than `1`.

## Requirements

- `2 <= n <= 100000`.
- Return `n` itself when `n` is prime.

## Source

- Source: FormalBenchHF base program `SmallestDivisor.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_smallest_divisor(n: i32) -> i32 {
    let mut i = 2;
    while i <= n / i { if n % i == 0 { return i; } i += 1; }
    n
}
```
