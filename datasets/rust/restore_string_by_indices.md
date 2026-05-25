# restore_string_by_indices

## Problem

Restore a string by placing `s[i]` at index `indices[i]`; indices are comma-separated integers.

## Requirements

- `indices` is a permutation of `0..len(s)-1`.
- `indices` is comma-separated with no spaces.
- Return a string `out` such that `out[indices[i]] == s[i]`.
- Input strings are ASCII.

## Source

- Source: LeetCode problem `shuffle-string`.
- URL: https://leetcode.com/problems/shuffle-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn restore_string_by_indices(s: &str, indices: &str) -> String {
    let sb = s.as_bytes();
    let parts: Vec<usize> = indices.split(',').map(|x| x.parse::<usize>().unwrap()).collect();
    let mut out = vec![0u8; sb.len()];
    for i in 0..sb.len() { out[parts[i]] = sb[i]; }
    String::from_utf8(out).unwrap()
}
```
