# LC Longest Substring Unique Length

## Problem

Return the length of the longest substring of `s` without repeated ASCII characters.

## Requirements

- `s` is ASCII.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `longest-substring-without-repeating-characters`.
- URL: https://leetcode.com/problems/longest-substring-without-repeating-characters/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_longest_substring_unique_len(s: &str) -> i32 {
    let mut last = [-1i32; 256];
    let mut left = 0i32;
    let mut best = 0i32;
    for (right, ch) in s.bytes().enumerate() { let r = right as i32; if last[ch as usize] >= left { left = last[ch as usize] + 1; } last[ch as usize] = r; if r - left + 1 > best { best = r - left + 1; } }
    best
}
```
