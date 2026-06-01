# SpecGenBench Dominant Index

## Problem

Return the index of the largest element if it is at least twice every other element; otherwise return `-1`.

## Requirements

- `n > 0` and `nums` has at least `n` elements.
- Use only the first `n` values.
- Products by `2` do not overflow.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/DominantIndex`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/DominantIndex/DominantIndex.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_dominant_index(n: i32, nums: &[i32]) -> i32 {
    let mut idx = 0;
    let mut i = 1;
    while i < n { if nums[i as usize] > nums[idx as usize] { idx = i; } i += 1; }
    i = 0;
    while i < n { if i != idx && nums[idx as usize] < 2 * nums[i as usize] { return -1; } i += 1; }
    idx
}
```
