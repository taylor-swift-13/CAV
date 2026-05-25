# fb_array_min_swaps_like

## Problem

Run the two-pointer FormalBench scan and return how many equal aligned pairs it counts.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FindMinSwaps.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_min_swaps_like(arr: &[i32], n: i32) -> i32 {
    let (mut count, mut i, mut j) = (0, 0usize, 1usize);
    while i < n as usize && j < n as usize {
        if arr[i] == arr[j] { i += 1; j += 1; count += 1; }
        else if arr[i] > arr[j] { i += 1; }
        else { j += 1; }
    }
    count
}
```
