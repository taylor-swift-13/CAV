# Exercism Sum Of Multiples 3 5

## Problem

Return the sum of positive integers below `limit` that are divisible by `3` or `5`.

## Requirements

- `limit >= 0`.
- Count each value once.

## Source

- Source: Exercism problem `sum-of-multiples`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/sum-of-multiples
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_sum_of_multiples_3_5(int limit) {
    int sum = 0;
    for (int i = 1; i < limit; i++) if (i % 3 == 0 || i % 5 == 0) sum += i;
    return sum;
}
```
