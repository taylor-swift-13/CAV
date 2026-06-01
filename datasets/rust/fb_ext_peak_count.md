# FormalBench Peak Count

## Problem

Return the number of strict interior peaks in the first `n` elements of `a`.

## Requirements

- `n >= 0` and `a` has at least `n` elements.
- Index `i` is a peak when `0 < i < n - 1` and `a[i]` is greater than both neighbors.
- Endpoints are never peaks.

## Source

- Source: FormalBench problem `FormalBenchHF/base/programs/FindPeak.java`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: local rewrite from SESpec java_flat.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_ext_peak_count(n: i32, a: &[i32]) -> i32 {
    let mut count = 0;
    let mut i = 1;
    while i + 1 < n {
        if a[i as usize] > a[(i - 1) as usize] && a[i as usize] > a[(i + 1) as usize] { count += 1; }
        i += 1;
    }
    count
}
```
