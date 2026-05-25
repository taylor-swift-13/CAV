# valid_parentheses_brackets

## Problem

Return true if `s` is a valid bracket string over `()[]{}`.

## Requirements

- Input contains only bracket characters.
- Every closing bracket must match the most recent unmatched opening bracket.
- Return true for the empty string.
- Maximum tested length is below 128.

## Source

- Source: LeetCode problem `valid-parentheses`.
- URL: https://leetcode.com/problems/valid-parentheses/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn valid_parentheses_brackets(s: &str) -> bool {
    let mut stack: Vec<u8> = Vec::new();
    for c in s.bytes() { if c == b'(' || c == b'[' || c == b'{' { stack.push(c); } else { let Some(o) = stack.pop() else { return false; }; if (c == b')' && o != b'(') || (c == b']' && o != b'[') || (c == b'}' && o != b'{') { return false; } } }
    stack.is_empty()
}
```
