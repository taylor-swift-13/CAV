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

```java
class ExMatrixRowSum {
    public static int ex_matrix_row_sum(String rows, int row) {
        String[] rs = rows.split(";"); int sum = 0; for (String p : rs[row - 1].split(",")) sum += Integer.parseInt(p); return sum;
    }
}
```
