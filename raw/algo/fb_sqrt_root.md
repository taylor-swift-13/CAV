# fb_sqrt_root

## Problem

Return the floor of the square root of `num`; return `-1` when `num` is negative.

## Requirements

- `-10000 <= num <= 10000`.
- Use integer arithmetic and return the floor for non-perfect squares.

## Source

- Source: FormalBenchHF base program `SqrtRoot.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_sqrt_root(int num) {
    if (num < 0) return -1;
    int left = 0, right = num;
    while (left <= right) {
        int mid = left + (right - left) / 2;
        if (mid * mid == num) return mid;
        if (mid * mid < num) left = mid + 1;
        else right = mid - 1;
    }
    return right;
}
```
