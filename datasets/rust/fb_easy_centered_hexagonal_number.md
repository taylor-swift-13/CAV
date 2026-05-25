# fb_easy_centered_hexagonal_number

## Problem

Return the FormalBench centered hexagonal number value for `n`.

## Requirements

- `0 <= n <= 10000`.
- Use the reference loop `r=1; while n>0 { n--; r += 6*n; }`.

## Source

- Source: FormalBenchHF base program `CenteredHexagonalNumber.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_centered_hexagonal_number(mut n: i32) -> i32 {
    let mut r = 1;
    while n > 0 { n -= 1; r += 6 * n; }
    r
}
```
