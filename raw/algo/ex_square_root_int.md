# Exercism Square Root Int

## Problem

Return the integer square root of a perfect-square radicand.

## Requirements

- `radicand >= 1`.
- The input is a perfect square.

## Source

- Source: Exercism problem `square-root`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/square-root
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_square_root_int(int radicand) {
    int x = 1;
    while (x * x < radicand) x++;
    return x;
}
```
