# fb_more_modular_inverse_square_count

## Problem

Count how many of the first `n` array values satisfy `(x*x) % p == 1`.

## Requirements

- Array length is at most `50`.
- `2 <= p <= 1000`.
- Array values are nonnegative and small enough that `x*x` fits in signed 32-bit integer.

## Source

- Source: FormalBenchHF base program `ModularInverse.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbMoreModularInverseSquareCount {
    public static int fb_more_modular_inverse_square_count(int[] arr, int n, int p) {
        int count = 0;
        for (int i = 0; i < n; i++) if ((arr[i] * arr[i]) % p == 1) count++;
        return count;
    }
}
```
