# SpecGenBench Number Of Cuts

## Problem

Return the minimum number of straight cuts needed to divide a circle into `n` equal slices under the benchmark rule.

## Requirements

- `n >= 1`.
- For `n == 1`, return `0`.
- For even `n`, return `n / 2`; for odd `n`, return `n`.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/NumberOfCuts`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/NumberOfCuts/NumberOfCuts.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sg_number_of_cuts(int n) {
    if (n == 1) return 0;
    if (n % 2 == 0) return n / 2;
    return n;
}
```
