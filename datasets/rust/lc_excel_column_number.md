# LC Excel Sheet Column Number

## Problem

Return the one-based column number for an Excel column title.

## Requirements

- `title` contains uppercase English letters.

## Source

- Source: LeetCode problem `excel-sheet-column-number`.
- URL: https://leetcode.com/problems/excel-sheet-column-number/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_excel_column_number(title: &str) -> i32 {
    let mut ans = 0; for b in title.bytes() { ans = ans * 26 + (b - b'A' + 1) as i32; } ans
}
```
