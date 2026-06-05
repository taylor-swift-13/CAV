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

```c
int lc_excel_column_number(const char *title) {
    int ans = 0; for (int i = 0; title[i] != '\0'; i++) ans = ans * 26 + title[i] - 'A' + 1; return ans;
}
```
