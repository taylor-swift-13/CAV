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

```rust
pub fn lc_valid_sudoku_rows(rows: &str) -> bool {
    let rs: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let mut row = [[false; 10]; 9]; let mut col = [[false; 10]; 9]; let mut boxs = [[false; 10]; 9];
    let mut r = 0usize; while r < 9 { let mut c = 0usize; while c < 9 { let ch = rs[r][c]; if ch != b'.' { let d = (ch - b'0') as usize; let b = (r / 3) * 3 + c / 3; if row[r][d] || col[c][d] || boxs[b][d] { return false; } row[r][d] = true; col[c][d] = true; boxs[b][d] = true; } c += 1; } r += 1; } true
}
```
