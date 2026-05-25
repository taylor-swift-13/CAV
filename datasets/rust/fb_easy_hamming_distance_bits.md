# fb_easy_hamming_distance_bits

## Problem

Return the number of bit positions where nonnegative integers `n1` and `n2` differ.

## Requirements

- `0 <= n1, n2 <= 1000000`.
- Compare binary representations until both numbers become zero.

## Source

- Source: FormalBenchHF base program `HammingDistance.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_easy_hamming_distance_bits(mut n1: i32, mut n2: i32) -> i32 {
    let mut count = 0;
    while n1 != 0 || n2 != 0 { if (n1 & 1) != (n2 & 1) { count += 1; } n1 >>= 1; n2 >>= 1; }
    count
}
```
