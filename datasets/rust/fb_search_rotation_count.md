# fb_search_rotation_count

## Problem

Return the rotation count of a sorted array that was rotated, or `0` when no pivot is found.

## Requirements

- `1 <= n <= a.length <= 50`.
- The first `n` elements are strictly increasing after some rotation.

## Source

- Source: FormalBenchHF base program `FindRotationCount.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_rotation_count(a: &[i32], n: i32) -> i32 {
    let (mut start, mut end) = (0, n - 1);
    while start <= end { let mid = start + (end - start) / 2; if mid < end && a[mid as usize] > a[mid as usize + 1] { return mid + 1; } if mid > start && a[mid as usize] < a[mid as usize - 1] { return mid; } if a[mid as usize] >= a[start as usize] { start = mid + 1; } else { end = mid - 1; } }
    0
}
```
