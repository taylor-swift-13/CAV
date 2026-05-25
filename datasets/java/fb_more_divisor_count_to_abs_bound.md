# fb_more_divisor_count_to_abs_bound

## Problem

Count positive integers up to `abs(y)` that divide `x`.

## Requirements

- `1 <= x <= 100000`.
- `-10000 <= y <= 10000`.
- Use only integer arithmetic.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FindDivisor.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbMoreDivisorCountToAbsBound {
    public static int fb_more_divisor_count_to_abs_bound(int x, int y) {
        if (y < 0) y = -y;
        int count = 0;
        for (int i = 1; i <= y; i++) if (x % i == 0) count++;
        return count;
    }
}
```
