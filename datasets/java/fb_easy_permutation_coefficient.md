# fb_easy_permutation_coefficient

## Problem

Return `nPk`, the number of ordered selections of `k` items from `n` items.

## Requirements

- `0 <= k <= n <= 12`.
- Use integer arithmetic.

## Source

- Source: FormalBenchHF base program `PermutationCoefficient.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyPermutationCoefficient {
    public static int fb_easy_permutation_coefficient(int n, int k) {
        int res = 1;
        for (int i = 1; i <= k; i++) res *= (n - i + 1);
        return res;
    }
}
```
