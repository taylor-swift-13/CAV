# SpecGenBench Dominant Index

## Problem

Return the index of the largest element if it is at least twice every other element; otherwise return `-1`.

## Requirements

- `n > 0` and `nums` has at least `n` elements.
- Use only the first `n` values.
- Products by `2` do not overflow.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/DominantIndex`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/DominantIndex/DominantIndex.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sg_dominant_index(int n, int *nums) {
    int idx = 0;
    for (int i = 1; i < n; i++) if (nums[i] > nums[idx]) idx = i;
    for (int i = 0; i < n; i++) if (i != idx && nums[idx] < 2 * nums[i]) return -1;
    return idx;
}
```
