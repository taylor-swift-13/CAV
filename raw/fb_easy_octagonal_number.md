# fb_easy_octagonal_number

## Problem

Return the `n`th value of the FormalBench octagonal-number recurrence.

## Requirements

- `0 <= n <= 1000`.
- Use `f[0]=0` and `f[i+1]=f[i]+6*i+1`.

## Source

- Source: FormalBenchHF base program `IsOctagonal.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_easy_octagonal_number(int n) {
    int value = 0;
    for (int i = 0; i <= n - 1; i++) value += 6 * i + 1;
    return value;
}
```
