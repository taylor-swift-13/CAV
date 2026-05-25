# substring_index_ascii

## Problem

Return the first index of `needle` in `haystack`, or `-1` if absent.

## Requirements

- Inputs are ASCII strings.
- Return a zero-based index.
- If `needle` is empty, return `0`.
- Use direct substring matching semantics.

## Source

- Source: LeetCode problem `find-the-index-of-the-first-occurrence-in-a-string`.
- URL: https://leetcode.com/problems/find-the-index-of-the-first-occurrence-in-a-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn substring_index_ascii(haystack: &str, needle: &str) -> i32 {
    if needle.is_empty() { return 0; }
    let h = haystack.as_bytes(); let n = needle.as_bytes();
    let mut i = 0usize; while i + n.len() <= h.len() { let mut ok = true; let mut j = 0usize; while j < n.len() { if h[i + j] != n[j] { ok = false; } j += 1; } if ok { return i as i32; } i += 1; }
    -1
}
```
