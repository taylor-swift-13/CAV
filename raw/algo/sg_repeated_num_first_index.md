# SpecGenBench Repeated Num First Index

## Problem

Return the first index `i` whose value appears again later in the first `n` elements; return `-1` if no value repeats.

## Requirements

- `n >= 0` and `arr` has at least `n` elements.
- Use nested scan order.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/RepeatedNumNested`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/RepeatedNumNested/RepeatedNumNested.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sg_repeated_num_first_index(int n, int *arr) {
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (arr[i] == arr[j]) return i;
    return -1;
}
```
