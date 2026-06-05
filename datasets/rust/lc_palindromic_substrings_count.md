# LC Palindromic Substrings Count

## Problem

Return the number of palindromic substrings of `s`.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `palindromic-substrings`.
- URL: https://leetcode.com/problems/palindromic-substrings/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_palindromic_substrings_count(s: &str) -> i32 {
    let b = s.as_bytes(); let n = b.len() as i32; let mut ans = 0; let mut center = 0; while center < 2 * n - 1 { let mut l = center / 2; let mut r = l + center % 2; while l >= 0 && r < n && b[l as usize] == b[r as usize] { ans += 1; l -= 1; r += 1; } center += 1; } ans
}
```
