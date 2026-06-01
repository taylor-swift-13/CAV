# Exercism Darts Score

## Problem

Return the dart score for integer coordinates using radii 1, 5, and 10.

## Requirements

- Coordinates are integer grid points.
- Use squared-distance comparisons to avoid floating point.

## Source

- Source: Exercism problem `darts`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/darts
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_darts_score(int x, int y) {
    int d = x * x + y * y; if (d <= 1) return 10; if (d <= 25) return 5; if (d <= 100) return 1; return 0;
}
```
