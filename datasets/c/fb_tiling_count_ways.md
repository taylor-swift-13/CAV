# fb_tiling_count_ways

## Problem

Return the FormalBench two-state tiling recurrence value `A[n]`, where `A[0]=1`, `A[1]=0`, `B[0]=0`, `B[1]=1`, `A[i]=A[i-2]+2*B[i-1]`, and `B[i]=A[i-1]+B[i-2]`.

## Requirements

- `1 <= n <= 20`.
- Return `A[n]`.

## Source

- Source: FormalBenchHF base program `CountWays.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_tiling_count_ways(int n) {
    int A[21] = {0};
    int B[21] = {0};
    A[0] = 1; A[1] = 0; B[0] = 0; B[1] = 1;
    for (int i = 2; i <= n; i++) {
        A[i] = A[i - 2] + 2 * B[i - 1];
        B[i] = A[i - 1] + B[i - 2];
    }
    return A[n];
}
```
