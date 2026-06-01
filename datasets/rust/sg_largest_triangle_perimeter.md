# SpecGenBench Largest Triangle Perimeter

## Problem

Return the largest possible perimeter of a nondegenerate triangle chosen from the first `n` side lengths, or `0` if none exists.

## Requirements

- `n >= 0` and `sides` has at least `n` elements.
- All side lengths are positive.
- The implementation may reorder a local copy.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/LargestPerimeter`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/LargestPerimeter/LargestPerimeter.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_largest_triangle_perimeter(n: i32, sides: &[i32]) -> i32 {
    let mut a = [0i32; 64];
    let mut i = 0;
    while i < n { a[i as usize] = sides[i as usize]; i += 1; }
    i = 0;
    while i < n { let mut j = i + 1; while j < n { if a[i as usize] > a[j as usize] { let t = a[i as usize]; a[i as usize] = a[j as usize]; a[j as usize] = t; } j += 1; } i += 1; }
    i = n - 1;
    while i >= 2 { if a[(i - 2) as usize] + a[(i - 1) as usize] > a[i as usize] { return a[(i - 2) as usize] + a[(i - 1) as usize] + a[i as usize]; } i -= 1; }
    0
}
```
