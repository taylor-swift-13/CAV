# fb_last_digit_product_range

## Problem

Return the last decimal digit of the product `(a+1) * (a+2) * ... * b`, with the special case `a == b` returning `1`.

## Requirements

- `0 <= a <= b <= 1000`.
- If `b - a >= 5`, return `0`.

## Source

- Source: FormalBenchHF base program `ComputeLastDigit.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_last_digit_product_range(a: i32, b: i32) -> i32 {
    if a == b { return 1; }
    if b - a >= 5 { return 0; }
    let mut value = 1;
    for i in (a + 1)..=b { value = (value * (i % 10)) % 10; }
    value % 10
}
```
