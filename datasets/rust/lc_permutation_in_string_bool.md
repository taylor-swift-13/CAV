# LC Permutation In String Bool

## Problem

Return true if `s2` contains any permutation of `s1` as a substring.

## Requirements

- Both strings contain lowercase English letters.

## Source

- Source: LeetCode problem `permutation-in-string`.
- URL: https://leetcode.com/problems/permutation-in-string/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_permutation_in_string_bool(s1: &str, s2: &str) -> bool {
    let a = s1.as_bytes(); let b = s2.as_bytes(); if a.len() > b.len() { return false; } let mut need = [0; 26]; let mut win = [0; 26]; let mut i = 0usize; while i < a.len() { need[(a[i] - b'a') as usize] += 1; win[(b[i] - b'a') as usize] += 1; i += 1; } let mut start = 0usize; while start + a.len() <= b.len() { if need == win { return true; } if start + a.len() < b.len() { win[(b[start] - b'a') as usize] -= 1; win[(b[start + a.len()] - b'a') as usize] += 1; } start += 1; } false
}
```
