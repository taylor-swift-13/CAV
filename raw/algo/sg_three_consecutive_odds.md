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

```c
int sg_three_consecutive_odds(int n, int *arr) {
    for (int i = 0; i + 2 < n; i++) if (arr[i] % 2 != 0 && arr[i + 1] % 2 != 0 && arr[i + 2] % 2 != 0) return 1;
    return 0;
}
```
