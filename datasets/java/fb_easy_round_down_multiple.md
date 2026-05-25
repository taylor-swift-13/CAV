# fb_easy_round_down_multiple

## Problem

Return the largest multiple of `m` that is less than or equal to `n`.

## Requirements

- `0 <= n <= 10000`.
- `1 <= m <= 1000`.

## Source

- Source: FormalBenchHF base program `RoundNum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyRoundDownMultiple {
    public static int fb_easy_round_down_multiple(int n, int m) {
        for (int i = n; i >= 0; i--) if (i % m == 0) return i;
        return -1;
    }
}
```
