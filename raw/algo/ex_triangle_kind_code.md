# Exercism Triangle Kind Code

## Problem

Classify a triangle by side lengths.

## Requirements

- Return `0` for invalid, `1` for equilateral, `2` for isosceles, and `3` for scalene.
- All sides are signed 32-bit integers.

## Source

- Source: Exercism problem `triangle`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/triangle
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_triangle_kind_code(int a, int b, int c) {
    if (a <= 0 || b <= 0 || c <= 0 || a + b <= c || a + c <= b || b + c <= a) return 0;
    if (a == b && b == c) return 1;
    if (a == b || a == c || b == c) return 2;
    return 3;
}
```
