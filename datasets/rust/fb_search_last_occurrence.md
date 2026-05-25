# fb_search_last_occurrence

## Problem

Return the last index of `x` in the sorted first `n` elements of `a`, or `-1` if absent.

## Requirements

- `0 <= n <= a.length <= 50`.
- The first `n` elements are sorted in nondecreasing order.

## Source

- Source: FormalBenchHF base program `FindLastOccurrence.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_last_occurrence(a: &[i32], n: i32, x: i32) -> i32 {
    let (mut low, mut high, mut result) = (0, n - 1, -1);
    while low <= high { let mid = (low + high) / 2; let v = a[mid as usize]; if v == x { result = mid; low = mid + 1; } else if v < x { low = mid + 1; } else { high = mid - 1; } }
    result
}
```
