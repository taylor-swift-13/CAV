# SpecGenBench Check A Before B

## Problem

Return true if every `a` in string `s` appears before every `b`.

## Requirements

- `s` contains only `a` and `b`.
- The empty string is allowed.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/CheckABeforeB`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/CheckABeforeB/CheckABeforeB.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_check_a_before_b(s: &str) -> bool {
    let mut seen_b = false;
    for ch in s.bytes() { if ch == b'b' { seen_b = true; } if ch == b'a' && seen_b { return false; } }
    true
}
```
