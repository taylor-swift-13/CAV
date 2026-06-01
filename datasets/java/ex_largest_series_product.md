# Exercism Largest Series Product

## Problem

Return the largest product of `span` adjacent digits in string `digits`.

## Requirements

- `digits` contains decimal digits only.
- `0 <= span <= length(digits)`.
- An empty span has product `1`.

## Source

- Source: Exercism problem `largest-series-product`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/largest-series-product
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExLargestSeriesProduct {
    public static int ex_largest_series_product(String digits, int span) {
        if (span == 0) return 1;
        int best = 0;
        for (int i = 0; i + span <= digits.length(); i++) { int p = 1; for (int j = 0; j < span; j++) p *= digits.charAt(i + j) - '0'; if (p > best) best = p; }
        return best;
    }
}
```
