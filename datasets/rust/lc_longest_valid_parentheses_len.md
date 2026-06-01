# LC Longest Valid Parentheses Length

## Problem

Return the length of the longest valid parentheses substring.

## Requirements

- `s` contains only `(` and `)`.

## Source

- Source: LeetCode problem `longest-valid-parentheses`.
- URL: https://leetcode.com/problems/longest-valid-parentheses/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_longest_valid_parentheses_len(s: &str) -> i32 {
    let mut st: Vec<i32> = vec![-1]; let mut best = 0; for (i, b) in s.bytes().enumerate() { if b == b'(' { st.push(i as i32); } else { st.pop(); if st.is_empty() { st.push(i as i32); } else { let len = i as i32 - *st.last().unwrap(); if len > best { best = len; } } } } best
}
```
