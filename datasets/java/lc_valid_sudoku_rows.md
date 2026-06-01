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

```java
class LcValidSudokuRows {
    public static boolean lc_valid_sudoku_rows(String rows) {
        boolean[][] row = new boolean[9][10], col = new boolean[9][10], box = new boolean[9][10]; String[] rs = rows.split(";");
        for (int r = 0; r < 9; r++) for (int c = 0; c < 9; c++) { char ch = rs[r].charAt(c); if (ch != '.') { int d = ch - '0'; int b = (r / 3) * 3 + c / 3; if (row[r][d] || col[c][d] || box[b][d]) return false; row[r][d] = col[c][d] = box[b][d] = true; } } return true;
    }
}
```
