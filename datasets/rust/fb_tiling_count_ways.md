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

```rust
pub fn fb_tiling_count_ways(n: i32) -> i32 {
    let n = n as usize;
    let mut a = vec![0; n + 1];
    let mut b = vec![0; n + 1];
    a[0] = 1; b[1] = 1;
    for i in 2..=n {
        a[i] = a[i - 2] + 2 * b[i - 1];
        b[i] = a[i - 1] + b[i - 2];
    }
    a[n]
}
```
