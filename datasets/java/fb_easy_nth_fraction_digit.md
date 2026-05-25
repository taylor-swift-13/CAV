# fb_easy_nth_fraction_digit

## Problem

Return the `n`th decimal digit after the decimal point in the fraction `p / q`.

## Requirements

- `0 <= p < q <= 1000`.
- `1 <= n <= 20`.

## Source

- Source: FormalBenchHF base program `FindNthDigit.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyNthFractionDigit {
    public static int fb_easy_nth_fraction_digit(int p, int q, int n) {
        int res = 0;
        while (n > 0) { n--; p *= 10; res = p / q; p %= q; }
        return res;
    }
}
```
