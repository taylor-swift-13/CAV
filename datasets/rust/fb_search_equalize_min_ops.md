# fb_search_equalize_min_ops

## Problem

Return the number of `k`-sized increments needed to raise all first `n` array elements to the maximum value, or `-1` if impossible.

## Requirements

- `1 <= n <= arr.length <= 50`.
- `k > 0`.

## Source

- Source: FormalBenchHF base program `MinOps.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_equalize_min_ops(arr: &[i32], n: i32, k: i32) -> i32 {
    let mut max = arr[0]; for i in 1..(n as usize) { if arr[i] > max { max = arr[i]; } }
    let mut res = 0; for i in 0..(n as usize) { if (max - arr[i]) % k != 0 { return -1; } res += (max - arr[i]) / k; }
    res
}
```
