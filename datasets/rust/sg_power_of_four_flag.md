# SpecGenBench Power Of Four Flag

## Problem

Return true if `n` is a positive power of four.

## Requirements

- `n` is a signed 32-bit integer.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/PowerOfFourLoop`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/PowerOfFourLoop/PowerOfFourLoop.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_power_of_four_flag(mut n: i32) -> bool {
    if n <= 0 { return false; }
    while n % 4 == 0 { n /= 4; }
    n == 1
}
```
