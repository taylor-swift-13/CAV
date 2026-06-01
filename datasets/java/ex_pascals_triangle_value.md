# Exercism Pascal Triangle Value

## Problem

Return the value at zero-based `row` and `col` in Pascal's triangle.

## Requirements

- `0 <= col <= row <= 30`.
- The result fits in signed 32-bit integer range.

## Source

- Source: Exercism problem `pascals-triangle`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/pascals-triangle
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExPascalsTriangleValue {
    public static int ex_pascals_triangle_value(int row, int col) {
        int[][] v = new int[row + 1][row + 1];
        for (int i = 0; i <= row; i++) { v[i][0] = 1; v[i][i] = 1; for (int j = 1; j < i; j++) v[i][j] = v[i - 1][j - 1] + v[i - 1][j]; }
        return v[row][col];
    }
}
```
