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

```c
int sg_overlap_area(int ax1, int ay1, int ax2, int ay2, int bx1, int by1, int bx2, int by2) {
    int w = (ax2 < bx2 ? ax2 : bx2) - (ax1 > bx1 ? ax1 : bx1);
    int h = (ay2 < by2 ? ay2 : by2) - (ay1 > by1 ? ay1 : by1);
    if (w < 0) w = 0;
    if (h < 0) h = 0;
    return w * h;
}
```
