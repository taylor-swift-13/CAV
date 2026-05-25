# fb_average_even_upto

## Problem

Return the integer average of all positive even integers from `1` through `n`.

## Requirements

- `2 <= n <= 10000`.
- Use truncating integer division.

## Source

- Source: FormalBenchHF base program `AverageEven.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbAverageEvenUpto {
    public static int fb_average_even_upto(int n) {
        int sum = 0, count = 0;
        for (int i = 1; i <= n; i++) if (i % 2 == 0) { sum += i; count++; }
        return sum / count;
    }
}
```
