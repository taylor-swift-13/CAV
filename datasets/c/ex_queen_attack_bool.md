# Exercism Queen Attack Bool

## Problem

Return true if two queens can attack each other.

## Requirements

- Coordinates are zero-based row/column pairs.
- Queens attack along the same row, column, or diagonal.

## Source

- Source: Exercism problem `queen-attack`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/queen-attack
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_queen_attack_bool(int r1, int c1, int r2, int c2) {
    int dr = r1 - r2, dc = c1 - c2; if (dr < 0) dr = -dr; if (dc < 0) dc = -dc; return r1 == r2 || c1 == c2 || dr == dc;
}
```
