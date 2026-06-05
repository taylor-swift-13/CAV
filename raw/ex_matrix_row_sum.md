# Exercism Matrix Row Sum

## Problem

Return the sum of a one-based row from a matrix string.

## Requirements

- Rows are semicolon-separated and values inside a row are comma-separated.
- `row` is one-based.

## Source

- Source: Exercism problem `matrix`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/matrix
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_matrix_row_sum(const char *rows, int row) {
    int current = 1, i = 0, sum = 0;
    while (rows[i] != '\0') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + (rows[i] - '0'); i++; } if (current == row) sum += sign * v; if (rows[i] == ';') { current++; i++; } else if (rows[i] == ',') i++; }
    return sum;
}
```
