# SpecGenBench Three Consecutive Odds

## Problem

Return true exactly when the first `n` array elements contain three adjacent odd values.

## Requirements

- `n >= 0` and `arr` has at least `n` elements.
- Negative odd numbers count as odd.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/ThreeConsecutiveOdds`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/ThreeConsecutiveOdds/ThreeConsecutiveOdds.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_three_consecutive_odds(n: i32, arr: &[i32]) -> bool {
    let mut i = 0;
    while i + 2 < n { if arr[i as usize] % 2 != 0 && arr[(i + 1) as usize] % 2 != 0 && arr[(i + 2) as usize] % 2 != 0 { return true; } i += 1; }
    false
}
```
