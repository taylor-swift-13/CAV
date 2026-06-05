# Exercism Difference Of Squares

## Problem

Return the square of the sum `1..n` minus the sum of squares `1^2..n^2`.

## Requirements

- `n >= 0`.
- The result fits in signed 32-bit integer range.

## Source

- Source: Exercism problem `difference-of-squares`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/difference-of-squares
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_difference_of_squares(int n) {
    int sum = n * (n + 1) / 2;
    int square_sum = n * (n + 1) * (2 * n + 1) / 6;
    return sum * sum - square_sum;
}
```
