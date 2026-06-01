# SpecGenBench Is Monotonic Array

## Problem

Return true if the first `n` values are monotone nondecreasing or monotone nonincreasing.

## Requirements

- `n >= 0` and `nums` has at least `n` elements.
- Arrays of length `0`, `1`, or `2` can be monotone.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/IsMonotonic`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/IsMonotonic/IsMonotonic.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_is_monotonic_array(n: i32, nums: &[i32]) -> bool {
    let mut inc = true; let mut dec = true; let mut i = 0;
    while i + 1 < n { if nums[i as usize] > nums[(i + 1) as usize] { inc = false; } if nums[i as usize] < nums[(i + 1) as usize] { dec = false; } i += 1; }
    inc || dec
}
```
