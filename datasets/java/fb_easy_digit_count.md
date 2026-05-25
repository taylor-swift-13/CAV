# fb_easy_digit_count

## Problem

Return the number of decimal digits in positive integer `n`.

## Requirements

- `1 <= n <= 1000000000`.
- Use repeated division by `10`.

## Source

- Source: FormalBenchHF base program `CountDigit.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyDigitCount {
    public static int fb_easy_digit_count(int n) {
        int count = 0;
        while (n > 0) { n /= 10; count++; }
        return count;
    }
}
```
