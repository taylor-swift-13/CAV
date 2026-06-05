# LC Valid Sudoku Rows

## Problem

Return true if a 9x9 Sudoku board has no repeated digit in any row, column, or 3x3 box.

## Requirements

- Rows are separated by semicolons.
- Each row has digits `1` to `9` or `.` for empty cells.

## Source

- Source: LeetCode problem `valid-sudoku`.
- URL: https://leetcode.com/problems/valid-sudoku/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_valid_sudoku_rows(const char *rows) {
    int row[9][10] = {{0}}, col[9][10] = {{0}}, box[9][10] = {{0}}, r = 0, c = 0;
    for (int i = 0; rows[i] != '\0'; i++) { if (rows[i] == ';') { r++; c = 0; continue; } if (rows[i] != '.') { int d = rows[i] - '0'; int b = (r / 3) * 3 + c / 3; if (row[r][d] || col[c][d] || box[b][d]) return 0; row[r][d] = col[c][d] = box[b][d] = 1; } c++; }
    return 1;
}
```
