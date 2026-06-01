# LC Minimum Add Parentheses Valid

## Problem

Return the minimum number of parentheses insertions needed to make `s` valid.

## Requirements

- `s` contains only `(` and `)`.

## Source

- Source: LeetCode problem `minimum-add-to-make-parentheses-valid`.
- URL: https://leetcode.com/problems/minimum-add-to-make-parentheses-valid/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_add_parentheses_valid(s: &str) -> i32 {
    let mut bal = 0; let mut add = 0; for b in s.bytes() { if b == b'(' { bal += 1; } else if bal > 0 { bal -= 1; } else { add += 1; } } add + bal
}
```
