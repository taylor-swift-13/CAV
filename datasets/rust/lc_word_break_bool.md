# LC Word Break Bool

## Problem

Return true if `s` can be segmented into dictionary words.

## Requirements

- Dictionary words are semicolon-separated.
- All strings are lowercase ASCII in the supplied tests.

## Source

- Source: LeetCode problem `word-break`.
- URL: https://leetcode.com/problems/word-break/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_word_break_bool(s: &str, dict: &str) -> bool {
    let words: Vec<&[u8]> = dict.split(';').map(|x| x.as_bytes()).collect(); let b = s.as_bytes(); let mut dp = vec![false; b.len() + 1]; dp[0] = true;
    let mut i = 0usize; while i < b.len() { if dp[i] { for w in &words { if i + w.len() <= b.len() && &b[i..i + w.len()] == *w { dp[i + w.len()] = true; } } } i += 1; } dp[b.len()]
}
```
