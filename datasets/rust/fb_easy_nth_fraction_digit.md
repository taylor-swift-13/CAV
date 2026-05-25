# fb_easy_nth_fraction_digit

## Problem

Return the `n`th decimal digit after the decimal point in the fraction `p / q`.

## Requirements

- `0 <= p < q <= 1000`.
- `1 <= n <= 20`.

## Source

- Source: FormalBenchHF base program `FindNthDigit.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_nth_fraction_digit(mut p: i32, q: i32, mut n: i32) -> i32 {
    let mut res = 0;
    while n > 0 { n -= 1; p *= 10; res = p / q; p %= q; }
    res
}
```
