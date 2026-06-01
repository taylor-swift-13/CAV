# SpecGenBench Repeated Char First Index

## Problem

Return the first index `i` whose character appears again later in lowercase string `s`; return `-1` if no character repeats.

## Requirements

- `s` contains lowercase English letters only.
- The empty string is allowed.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/RepeatedCharNested`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/RepeatedCharNested/RepeatedCharNested.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_repeated_char_first_index(s: &str) -> i32 {
    let b = s.as_bytes();
    let mut i = 0usize;
    while i < b.len() { let mut j = i + 1; while j < b.len() { if b[i] == b[j] { return i as i32; } j += 1; } i += 1; }
    -1
}
```
