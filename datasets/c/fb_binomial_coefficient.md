# fb_binomial_coefficient

## Problem

Return the binomial coefficient `C(n, k)`.

## Requirements

- `0 <= k <= n <= 20`.
- Use integer arithmetic.

## Source

- Source: FormalBenchHF base program `BinomialCoeff.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_binomial_coefficient(int n, int k) {
    if (k > n - k) k = n - k;
    int c = 1;
    for (int i = 1; i <= k; i++) c = c * (n - i + 1) / i;
    return c;
}
```
