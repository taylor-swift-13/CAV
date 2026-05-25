# fb_array_subarray_product_sum

## Problem

Return the sum of products of every contiguous subarray in the first `n` elements.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `SumOfSubarrayProd.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_subarray_product_sum(arr: &[i32], n: i32) -> i32 {
    let mut sum = 0;
    for i in 0..(n as usize) { let mut product = 1; for j in i..(n as usize) { product *= arr[j]; sum += product; } }
    sum
}
```
