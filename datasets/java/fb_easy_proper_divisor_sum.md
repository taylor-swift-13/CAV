# fb_easy_proper_divisor_sum

## Problem

Return the sum of all proper positive divisors of `number`.

## Requirements

- `1 <= number <= 10000`.
- Do not include `number` itself.

## Source

- Source: FormalBenchHF base program `SumDiv.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyProperDivisorSum {
    public static int fb_easy_proper_divisor_sum(int number) {
        int sum = 0;
        for (int i = 1; i <= number / 2; i++) if (number % i == 0) sum += i;
        return sum;
    }
}
```
