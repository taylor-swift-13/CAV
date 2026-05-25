# fb_more_factor_pair_count

## Problem

Count factor pairs of `n` found by scanning divisors from `2` through `sqrt(n)`, with the FormalBench special case `n == 1` returning `1`.

## Requirements

- `1 <= n <= 100000`.
- Use only integer arithmetic.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `CountFac.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_more_factor_pair_count(n: i32) -> i32 {
    let mut count = 0;
    if n == 1 { return 1; }
    let mut i = 2;
    while i <= n / i { if n % i == 0 { count += 1; if n / i == i { break; } } i += 1; }
    count
}
```
