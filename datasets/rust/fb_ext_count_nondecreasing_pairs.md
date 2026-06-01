# FormalBench Count Nondecreasing Pairs

## Problem

Return how many unordered index pairs `i < j` in the first `n` elements satisfy `a[i] <= a[j]`.

## Requirements

- `n >= 0` and `a` has at least `n` elements.
- Count each pair once.
- The result fits in a signed 32-bit integer.

## Source

- Source: FormalBench problem `FormalBenchHF/base/programs/CountPairs.java`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: local rewrite from SESpec java_flat.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_ext_count_nondecreasing_pairs(n: i32, a: &[i32]) -> i32 {
    let mut count = 0;
    let mut i = 0;
    while i < n {
        let mut j = i + 1;
        while j < n {
            if a[i as usize] <= a[j as usize] { count += 1; }
            j += 1;
        }
        i += 1;
    }
    count
}
```
