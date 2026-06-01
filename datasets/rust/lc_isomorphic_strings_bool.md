# LC Isomorphic Strings Bool

## Problem

Return true if two ASCII strings are isomorphic.

## Requirements

- Both strings have the same length.
- A bijection between characters must preserve order.

## Source

- Source: LeetCode problem `isomorphic-strings`.
- URL: https://leetcode.com/problems/isomorphic-strings/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_isomorphic_strings_bool(s: &str, t: &str) -> bool {
    let sb = s.as_bytes(); let tb = t.as_bytes(); let mut st = [0usize; 256]; let mut ts = [0usize; 256]; let mut i = 0usize; while i < sb.len() { let a = sb[i] as usize; let b = tb[i] as usize; if st[a] != ts[b] { return false; } st[a] = i + 1; ts[b] = i + 1; i += 1; } true
}
```
