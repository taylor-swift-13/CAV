# SpecGenBench Unique Num First Index

## Problem

Return the first index whose value appears exactly once in the first `n` elements; return `-1` if no such value exists.

## Requirements

- `n >= 0` and `arr` has at least `n` elements.
- Use nested scan order.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/UniqueNumNested`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/UniqueNumNested/UniqueNumNested.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_unique_num_first_index(n: i32, arr: &[i32]) -> i32 {
    let mut i = 0;
    while i < n { let mut found = false; let mut j = 0; while j < n { if i != j && arr[i as usize] == arr[j as usize] { found = true; } j += 1; } if !found { return i; } i += 1; }
    -1
}
```
