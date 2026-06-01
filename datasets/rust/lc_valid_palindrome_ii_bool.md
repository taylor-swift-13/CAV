# LC Valid Palindrome II Bool

## Problem

Return true if `s` can be a palindrome after deleting at most one character.

## Requirements

- Input is lowercase ASCII.

## Source

- Source: LeetCode problem `valid-palindrome-ii`.
- URL: https://leetcode.com/problems/valid-palindrome-ii/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_valid_palindrome_ii_bool(s: &str) -> bool {
    fn ok(b: &[u8], mut l: usize, mut r: usize) -> bool { while l < r { if b[l] != b[r] { return false; } l += 1; r -= 1; } true }
    let b = s.as_bytes(); let mut l = 0usize; let mut r = b.len() - 1; while l < r { if b[l] != b[r] { return ok(b, l + 1, r) || ok(b, l, r - 1); } l += 1; r -= 1; } true
}
```
