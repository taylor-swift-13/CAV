# SpecGenBench Boomerang Points

## Problem

Return true if three 2D points are not collinear.

## Requirements

- Coordinates fit in signed 32-bit integers.
- Cross-product intermediate results fit in signed 32-bit integers.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/IsBoomerang`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/IsBoomerang/IsBoomerang.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_is_boomerang_points(x1: i32, y1: i32, x2: i32, y2: i32, x3: i32, y3: i32) -> bool {
    (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1) != 0
}
```
