# Exercism Series Largest Digit Sum

## Problem

Return the largest sum of `span` adjacent digits in `digits`.

## Requirements

- `digits` contains decimal digits only.
- `0 <= span <= length(digits)`.
- An empty span has sum `0`.

## Source

- Source: Exercism problem `series`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/series
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExSeriesLargestDigitSum {
    public static int ex_series_largest_digit_sum(String digits, int span) {
        if (span == 0) return 0;
        int best = 0;
        for (int i = 0; i + span <= digits.length(); i++) { int sum = 0; for (int j = 0; j < span; j++) sum += digits.charAt(i + j) - '0'; if (sum > best) best = sum; }
        return best;
    }
}
```
