# SpecGenBench Repeated Num First Index

## Problem

Return the first index `i` whose value appears again later in the first `n` elements; return `-1` if no value repeats.

## Requirements

- `n >= 0` and `arr` has at least `n` elements.
- Use nested scan order.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/RepeatedNumNested`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/RepeatedNumNested/RepeatedNumNested.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_repeated_num_first_index(n: i32, arr: &[i32]) -> i32 {
    let mut i = 0;
    while i < n { let mut j = i + 1; while j < n { if arr[i as usize] == arr[j as usize] { return i; } j += 1; } i += 1; }
    -1
}
```
