# fb_search_insertion_index

## Problem

Return the index of `x` in sorted `a` if present; otherwise return the left insertion index.

## Requirements

- `0 <= n <= a.length <= 50`.
- The first `n` elements are sorted.

## Source

- Source: FormalBenchHF base program `LeftInsertion.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_insertion_index(a: &[i32], n: i32, x: i32) -> i32 {
    let (mut left, mut right) = (0, n - 1);
    while left <= right { let mid = (left + right) / 2; let v = a[mid as usize]; if v == x { return mid; } else if v < x { left = mid + 1; } else { right = mid - 1; } }
    left
}
```
