# SpecGenBench Is Monotonic Array

## Problem

Return true if the first `n` values are monotone nondecreasing or monotone nonincreasing.

## Requirements

- `n >= 0` and `nums` has at least `n` elements.
- Arrays of length `0`, `1`, or `2` can be monotone.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/IsMonotonic`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/IsMonotonic/IsMonotonic.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sg_is_monotonic_array(int n, int *nums) {
    int inc = 1, dec = 1;
    for (int i = 0; i + 1 < n; i++) { if (nums[i] > nums[i + 1]) inc = 0; if (nums[i] < nums[i + 1]) dec = 0; }
    return inc || dec;
}
```
