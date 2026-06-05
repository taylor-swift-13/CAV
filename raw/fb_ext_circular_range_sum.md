# FormalBench Circular Range Sum

## Problem

Return the sum collected by walking from index `left` to index `right` in a circular array.

## Requirements

- `n > 0` and `a` has at least `n` elements.
- `0 <= left, right < n`.
- Include both endpoints.
- The result fits in a signed 32-bit integer.

## Source

- Source: FormalBench problem `FormalBenchHF/base/programs/SumRangeList.java`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: local rewrite from SESpec java_flat.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_ext_circular_range_sum(int n, int *a, int left, int right) {
    int sum = 0;
    int i = left;
    while (1) {
        sum += a[i];
        if (i == right) break;
        i++;
        if (i == n) i = 0;
    }
    return sum;
}
```
