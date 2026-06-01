# LC Find All Anagrams Count

## Problem

Return how many start positions in `s` are anagrams of `p`.

## Requirements

- `s` and `p` contain lowercase English letters.

## Source

- Source: LeetCode problem `find-all-anagrams-in-a-string`.
- URL: https://leetcode.com/problems/find-all-anagrams-in-a-string/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_find_anagrams_count(s: &str, p: &str) -> i32 {
    let sb = s.as_bytes(); let pb = p.as_bytes(); if pb.len() > sb.len() { return 0; } let mut need = [0; 26]; let mut win = [0; 26]; let mut i = 0usize; while i < pb.len() { need[(pb[i] - b'a') as usize] += 1; win[(sb[i] - b'a') as usize] += 1; i += 1; } let mut ans = 0; let mut start = 0usize; while start + pb.len() <= sb.len() { if need == win { ans += 1; } if start + pb.len() < sb.len() { win[(sb[start] - b'a') as usize] -= 1; win[(sb[start + pb.len()] - b'a') as usize] += 1; } start += 1; } ans
}
```
