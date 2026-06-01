# Exercism Grains Square Value

## Problem

Return how many grains are on chessboard square `square` when the first square has 1 grain and each square doubles.

## Requirements

- `1 <= square <= 30`.
- The result fits in signed 32-bit integer range.

## Source

- Source: Exercism problem `grains`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/grains
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExGrainsSquareValue {
    public static int ex_grains_square_value(int square) {
        int value = 1;
        for (int i = 1; i < square; i++) value *= 2;
        return value;
    }
}
```
