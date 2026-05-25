# valid_palindrome_ascii

## Problem

Return true if ASCII string `s` is a palindrome after ignoring non-alphanumeric characters and case.

## Requirements

- `s` contains only ASCII characters for this dataset variant.
- Ignore every character that is not `[A-Za-z0-9]`.
- Letter comparison is case-insensitive; digit comparison is exact.
- The empty filtered string is a palindrome and must return true.
- The original string must not be modified.

## Source

- Source: LeetCode problem `valid-palindrome`.
- URL: https://leetcode.com/problems/valid-palindrome/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn valid_palindrome_ascii(s: &str) -> bool {
    let bytes = s.as_bytes();
    if bytes.is_empty() { return true; }
    let mut l: usize = 0;
    let mut r: usize = bytes.len() - 1;
    while l < r {
        let mut a = bytes[l];
        let mut b = bytes[r];
        let aa = a.is_ascii_alphanumeric();
        let bb = b.is_ascii_alphanumeric();
        if !aa { l += 1; continue; }
        if !bb { r -= 1; continue; }
        a = a.to_ascii_lowercase();
        b = b.to_ascii_lowercase();
        if a != b { return false; }
        l += 1;
        r -= 1;
    }
    true
}
```
