# fb_cal_sum

## Problem

Compute the FormalBench recurrence sum with base results `3, 3, 5` and transition `d = a + b` while rotating `(a, b, c)` to `(b, c, d)`.

## Requirements

- `0 <= n <= 20`.
- Follow the recurrence exactly as stated.

## Source

- Source: FormalBenchHF base program `CalSum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbCalSum {
    public static int fb_cal_sum(int n) {
        if (n == 0 || n == 1) return 3;
        if (n == 2) return 5;
        int sum = 5, a = 3, b = 0, c = 2;
        while (n > 2) {
            int d = a + b;
            sum += d;
            a = b; b = c; c = d;
            n--;
        }
        return sum;
    }
}
```
