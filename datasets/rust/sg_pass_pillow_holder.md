# SpecGenBench Pass Pillow Holder

## Problem

Return who holds a pillow after `time` seconds when it moves from person `1` to `n` and then reverses direction repeatedly.

## Requirements

- `n >= 2`.
- `time >= 0`.
- The pillow moves one position per second.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/PassPillow`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/PassPillow/PassPillow.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_pass_pillow_holder(n: i32, mut time: i32) -> i32 {
    let period = (n - 1) * 2;
    time %= period;
    if time < n { return time + 1; }
    n * 2 - time - 1
}
```
