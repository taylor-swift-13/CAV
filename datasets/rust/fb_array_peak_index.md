# fb_array_peak_index

## Problem

Return a peak index found by the FormalBench binary scan.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FindPeak.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_peak_index(arr: &[i32], n: i32) -> i32 {
    let (mut left, mut right) = (0usize, n as usize - 1);
    while left < right { let mid = left + (right - left) / 2; if arr[mid] < arr[mid + 1] { left = mid + 1; } else { right = mid; } }
    left as i32
}
```
