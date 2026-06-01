# SpecGenBench Rectangle Overlap Area

## Problem

Return the area of the intersection of two axis-aligned rectangles.

## Requirements

- Each rectangle is given by lower-left and upper-right corners.
- `ax1 <= ax2`, `ay1 <= ay2`, `bx1 <= bx2`, and `by1 <= by2`.
- Intermediate areas fit in signed 32-bit integer range.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/ComputeOverlap`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/ComputeOverlap/ComputeOverlap.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_overlap_area(ax1: i32, ay1: i32, ax2: i32, ay2: i32, bx1: i32, by1: i32, bx2: i32, by2: i32) -> i32 {
    let mut w = (if ax2 < bx2 { ax2 } else { bx2 }) - (if ax1 > bx1 { ax1 } else { bx1 });
    let mut h = (if ay2 < by2 { ay2 } else { by2 }) - (if ay1 > by1 { ay1 } else { by1 });
    if w < 0 { w = 0; }
    if h < 0 { h = 0; }
    w * h
}
```
