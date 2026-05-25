# fb_sum_even_factors

## Problem

Return the sum of all positive even divisors of `n`, excluding `1`.

## Requirements

- `1 <= n <= 10000`.
- Count each divisor once.

## Source

- Source: FormalBenchHF base program `Sumoffactors.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbSumEvenFactors {
    public static int fb_sum_even_factors(int n) {
        int sum = 0;
        for (int i = 2; i <= n; i++) if (n % i == 0 && i % 2 == 0) sum += i;
        return sum;
    }
}
```
