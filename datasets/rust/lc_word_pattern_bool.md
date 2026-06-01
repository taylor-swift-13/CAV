# LC Word Pattern Bool

## Problem

Return true if pattern letters bijectively match the words in `s`.

## Requirements

- Words in `s` are separated by single spaces.
- Pattern is lowercase ASCII.

## Source

- Source: LeetCode problem `word-pattern`.
- URL: https://leetcode.com/problems/word-pattern/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_word_pattern_bool(pattern: &str, s: &str) -> bool {
    let words: Vec<&str> = s.split(' ').collect(); let p = pattern.as_bytes(); if p.len() != words.len() { return false; } let mut i = 0usize; while i < p.len() { let mut j = i + 1; while j < p.len() { if (p[i] == p[j]) != (words[i] == words[j]) { return false; } j += 1; } i += 1; } true
}
```
