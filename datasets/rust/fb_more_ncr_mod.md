# fb_more_ncr_mod

## Problem

Return `C(n, r) mod p`, with `0` returned when `n < r`.

## Requirements

- `0 <= r <= 12`.
- `0 <= n <= 20`.
- `2 <= p <= 1000`.

## Source

- Source: FormalBenchHF base program `NcrModP.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_more_ncr_mod(n: i32, r: i32, p: i32) -> i32 {
    if n < r { return 0; }
    let mut ncr = 1;
    for i in 1..=r { ncr = (ncr * (n - i + 1)) / i; }
    ncr % p
}
```
