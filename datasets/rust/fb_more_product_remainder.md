# fb_more_product_remainder

## Problem

Return the product of the first `lens` elements of `arr`, modulo `n`.

## Requirements

- Array length is at most `20`.
- `1 <= n <= 100000`.
- The product fits in signed 64-bit integer for the stated tests.

## Source

- Source: FormalBenchHF base program `FindRemainder.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_more_product_remainder(arr: &[i32], lens: i32, n: i32) -> i32 {
    let mut product: i64 = 1;
    for i in 0..(lens as usize) { product *= arr[i] as i64; }
    (product % n as i64) as i32
}
```
