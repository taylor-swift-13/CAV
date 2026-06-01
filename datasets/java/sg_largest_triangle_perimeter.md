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

```java
class SgLargestTrianglePerimeter {
    public static int sg_largest_triangle_perimeter(int n, int[] sides) {
        int[] a = new int[n];
        for (int i = 0; i < n; i++) a[i] = sides[i];
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (a[i] > a[j]) { int t = a[i]; a[i] = a[j]; a[j] = t; }
        for (int i = n - 1; i >= 2; i--) if (a[i - 2] + a[i - 1] > a[i]) return a[i - 2] + a[i - 1] + a[i];
        return 0;
    }
}
```
