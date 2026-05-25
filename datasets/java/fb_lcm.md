# fb_lcm

## Problem

Return the least common multiple of positive integers `x` and `y`.

## Requirements

- `1 <= x, y <= 10000`.
- Return the answer as a signed 32-bit integer.

## Source

- Source: FormalBenchHF base program `Lcm.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbLcm {
    public static int fb_lcm(int x, int y) {
        int a = x, b = y;
        if (a > b) { int t = a; a = b; b = t; }
        int gcd = 1;
        for (int i = 1; i <= a; i++) if (a % i == 0 && b % i == 0) gcd = i;
        return (x * y) / gcd;
    }
}
```
