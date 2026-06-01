# LC Score Of Parentheses Value

## Problem

Return the score of a balanced parentheses string.

## Requirements

- Score rules are `()` = 1, concatenation sums, and wrapping doubles.

## Source

- Source: LeetCode problem `score-of-parentheses`.
- URL: https://leetcode.com/problems/score-of-parentheses/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_score_parentheses_value(s: &str) -> i32 {
    let b = s.as_bytes(); let mut ans = 0; let mut depth = 0; let mut i = 0usize; while i < b.len() { if b[i] == b'(' { depth += 1; } else { depth -= 1; if i > 0 && b[i - 1] == b'(' { ans += 1 << depth; } } i += 1; } ans
}
```
