# SpecGenBench All Unique Lowercase

## Problem

Return true if lowercase string `s` contains no repeated character.

## Requirements

- `s` contains lowercase English letters only.
- Strings longer than `26` must return false.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/IsAllUnique`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/IsAllUnique/IsAllUnique.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_all_unique_lowercase(s: &str) -> bool {
    let mut seen: i32 = 0;
    if s.len() > 26 { return false; }
    for ch in s.bytes() { let bit = 1 << (ch - b'a'); if (seen & bit) != 0 { return false; } seen |= bit; }
    true
}
```
