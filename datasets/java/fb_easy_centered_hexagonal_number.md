# fb_easy_centered_hexagonal_number

## Problem

Return the FormalBench centered hexagonal number value for `n`.

## Requirements

- `0 <= n <= 10000`.
- Use the reference loop `r=1; while n>0 { n--; r += 6*n; }`.

## Source

- Source: FormalBenchHF base program `CenteredHexagonalNumber.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyCenteredHexagonalNumber {
    public static int fb_easy_centered_hexagonal_number(int n) {
        int r = 1;
        while (n > 0) { n--; r += 6 * n; }
        return r;
    }
}
```
