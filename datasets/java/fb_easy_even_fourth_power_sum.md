# fb_easy_even_fourth_power_sum

## Problem

Return the sum of the fourth powers of the first `n` positive even numbers.

## Requirements

- `0 <= n <= 50`.
- The `i`th term is `(2*i)^4`.

## Source

- Source: FormalBenchHF base program `EvenPowerSum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyEvenFourthPowerSum {
    public static int fb_easy_even_fourth_power_sum(int n) {
        int sum = 0;
        for (int i = 1; i <= n; i++) { int j = 2 * i; sum += j * j * j * j; }
        return sum;
    }
}
```
