# LC Longest Palindrome Length

## Problem

Return the length of the longest palindrome that can be built from the letters of `s`.

## Requirements

- Input is ASCII letters.

## Source

- Source: LeetCode problem `longest-palindrome`.
- URL: https://leetcode.com/problems/longest-palindrome/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_longest_palindrome_len(s: &str) -> i32 {
    let mut cnt = [0i32; 128]; for b in s.bytes() { cnt[b as usize] += 1; } let mut ans = 0; let mut odd = 0; for v in cnt { ans += v / 2 * 2; if v % 2 == 1 { odd = 1; } } ans + odd
}
```
