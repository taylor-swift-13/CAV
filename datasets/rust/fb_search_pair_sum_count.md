# fb_search_pair_sum_count

## Problem

Return how many unordered pairs in the first `n` elements of `arr` sum to `target`.

## Requirements

- `0 <= n <= arr.length <= 50`.
- Array values are signed 32-bit integers.

## Source

- Source: FormalBenchHF base program `GetPairsCount.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_pair_sum_count(arr: &[i32], n: i32, target: i32) -> i32 {
    let mut count = 0;
    for i in 0..(n as usize) { for j in (i + 1)..(n as usize) { if arr[i] + arr[j] == target { count += 1; } } }
    count
}
```
