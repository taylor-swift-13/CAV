# fb_array_fixed_point

## Problem

For a sorted array, return an index `i` such that `arr[i] == i`, or `-1` if none exists.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FindFixedPoint.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_array_fixed_point(arr: &[i32], n: i32) -> i32 {
    let (mut start, mut end) = (0, n - 1);
    while start <= end { let mid = start + (end - start) / 2; let value = arr[mid as usize]; if value == mid { return mid; } else if value < mid { start = mid + 1; } else { end = mid - 1; } }
    -1
}
```
