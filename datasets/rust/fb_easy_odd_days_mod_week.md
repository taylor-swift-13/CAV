# fb_easy_odd_days_mod_week

## Problem

Return the FormalBench odd-days value for the first `n` years modulo `7`.

## Requirements

- `0 <= n <= 10000`.
- Use the leap-year adjustment from the reference recurrence.

## Source

- Source: FormalBenchHF base program `OddDays.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_odd_days_mod_week(mut n: i32) -> i32 {
    let hund1 = n / 100; let hund4 = n / 400; let mut leap = n / 4; let mut ordinary = n - leap;
    if hund1 != 0 { ordinary += hund1; leap -= hund1; }
    if hund4 != 0 { ordinary -= hund4; leap += hund4; }
    (ordinary + leap * 2) % 7
}
```
