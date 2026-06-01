# Exercism Allergies Score Count

## Problem

Return how many of the standard 8 allergy flags are present in `score`.

## Requirements

- Use bit positions 0 through 7 only.
- `score >= 0`.

## Source

- Source: Exercism problem `allergies`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/allergies
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExAllergiesScoreCount {
    public static int ex_allergies_score_count(int score) {
        int count = 0;
        for (int i = 0; i < 8; i++) if ((score & (1 << i)) != 0) count++;
        return count;
    }
}
```
