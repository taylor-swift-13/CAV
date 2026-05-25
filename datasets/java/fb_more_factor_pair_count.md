# fb_more_factor_pair_count

## Problem

Count factor pairs of `n` found by scanning divisors from `2` through `sqrt(n)`, with the FormalBench special case `n == 1` returning `1`.

## Requirements

- `1 <= n <= 100000`.
- Use only integer arithmetic.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `CountFac.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbMoreFactorPairCount {
    public static int fb_more_factor_pair_count(int n) {
        int count = 0;
        if (n == 1) return 1;
        for (int i = 2; i <= n / i; i++) { if (n % i == 0) { count++; if (n / i == i) break; } }
        return count;
    }
}
```
