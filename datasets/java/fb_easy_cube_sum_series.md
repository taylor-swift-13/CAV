# fb_easy_cube_sum_series

## Problem

Return `1^3 + 2^3 + ... + number^3`.

## Requirements

- `0 <= number <= 1000`.
- Return `0` when `number` is `0`.

## Source

- Source: FormalBenchHF base program `SumSeries.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyCubeSumSeries {
    public static int fb_easy_cube_sum_series(int number) {
        int sum = 0;
        for (int i = 1; i <= number; i++) sum += i * i * i;
        return sum;
    }
}
```
