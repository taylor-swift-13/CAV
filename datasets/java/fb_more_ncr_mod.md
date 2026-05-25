# fb_more_ncr_mod

## Problem

Return `C(n, r) mod p`, with `0` returned when `n < r`.

## Requirements

- `0 <= r <= 12`.
- `0 <= n <= 20`.
- `2 <= p <= 1000`.

## Source

- Source: FormalBenchHF base program `NcrModP.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbMoreNcrMod {
    public static int fb_more_ncr_mod(int n, int r, int p) {
        if (n < r) return 0;
        int ncr = 1;
        for (int i = 1; i <= r; i++) ncr = (ncr * (n - i + 1)) / i;
        return ncr % p;
    }
}
```
