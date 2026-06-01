# LC Find The Difference ASCII

## Problem

Return the ASCII code of the extra character in `t` compared with `s`.

## Requirements

- `t` is formed by shuffling `s` and adding one extra lowercase letter.

## Source

- Source: LeetCode problem `find-the-difference`.
- URL: https://leetcode.com/problems/find-the-difference/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_find_difference_ascii(s: &str, t: &str) -> i32 {
    let mut x = 0u8; for b in s.bytes() { x ^= b; } for b in t.bytes() { x ^= b; } x as i32
}
```
