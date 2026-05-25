# merge_strings_alternately_ascii

## Problem

Merge `word1` and `word2` by alternating characters, starting with `word1`.

## Requirements

- Inputs are ASCII strings.
- Take one character from `word1`, then one from `word2`, repeatedly.
- Append the remaining suffix of the longer string.
- The empty string is allowed.

## Source

- Source: LeetCode problem `merge-strings-alternately`.
- URL: https://leetcode.com/problems/merge-strings-alternately/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn merge_strings_alternately_ascii(word1: &str, word2: &str) -> String {
    let a = word1.as_bytes(); let b = word2.as_bytes(); let mut out: Vec<u8> = Vec::new(); let limit = if a.len() > b.len() { a.len() } else { b.len() };
    for i in 0..limit { if i < a.len() { out.push(a[i]); } if i < b.len() { out.push(b[i]); } }
    String::from_utf8(out).unwrap()
}
```
