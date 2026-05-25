# valid_anagram_ascii

## Problem

Return true if lowercase strings `a` and `b` are anagrams of each other.

## Requirements

- Inputs contain lowercase English letters only.
- The empty string is allowed.
- Return true exactly when both strings contain each letter the same number of times.
- No sorting is required.

## Source

- Source: LeetCode problem `valid-anagram`.
- URL: https://leetcode.com/problems/valid-anagram/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn valid_anagram_ascii(a: &str, b: &str) -> bool {
    let mut count = [0i32; 26];
    for x in a.bytes() { count[(x - b'a') as usize] += 1; }
    for x in b.bytes() { count[(x - b'a') as usize] -= 1; }
    count.iter().all(|&v| v == 0)
}
```
