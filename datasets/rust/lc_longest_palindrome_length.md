# LC Longest Palindrome Length

## Problem

Return the length of the longest palindromic contiguous substring of ASCII string `s`.

## Requirements

- The empty string returns `0`.
- Compare characters by byte value.
- Return only the length, not the substring itself.

## Source

- Source: LeetCode problem `longest-palindromic-substring`.
- URL: https://leetcode.com/problems/longest-palindromic-substring/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_longest_palindrome_length(s: &str) -> i32 {
    let bytes = s.as_bytes();
    let len = bytes.len() as i32;
    let mut best = 0;
    let mut center = 0;
    while center < len {
        let mut l = center;
        let mut r = center;
        while l >= 0 && r < len && bytes[l as usize] == bytes[r as usize] {
            let size = r - l + 1;
            if size > best { best = size; }
            l -= 1;
            r += 1;
        }
        l = center;
        r = center + 1;
        while l >= 0 && r < len && bytes[l as usize] == bytes[r as usize] {
            let size = r - l + 1;
            if size > best { best = size; }
            l -= 1;
            r += 1;
        }
        center += 1;
    }
    best
}
```
