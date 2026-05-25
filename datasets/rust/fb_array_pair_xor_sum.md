# fb_array_pair_xor_sum

## Problem

Return the sum of bitwise XOR over all unordered pairs in the first `n` elements.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `PairOrSum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_pair_xor_sum(arr: &[i32], n: i32) -> i32 {
    let mut sum = 0;
    for i in 0..(n as usize) { for j in (i + 1)..(n as usize) { sum += arr[i] ^ arr[j]; } }
    sum
}
```
