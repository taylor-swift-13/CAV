# fb_array_odd_xor_pair_count

## Problem

Return how many unordered pairs have an odd bitwise XOR.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FindOddPair.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_odd_xor_pair_count(a: &[i32], n: i32) -> i32 {
    let mut count = 0;
    for i in 0..(n as usize) { for j in (i + 1)..(n as usize) { if (a[i] ^ a[j]) % 2 == 1 { count += 1; } } }
    count
}
```
