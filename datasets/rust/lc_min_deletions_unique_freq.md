# LC Minimum Deletions Unique Frequencies

## Problem

Return the minimum deletions needed so every nonzero character frequency is unique.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `minimum-deletions-to-make-character-frequencies-unique`.
- URL: https://leetcode.com/problems/minimum-deletions-to-make-character-frequencies-unique/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_deletions_unique_freq(s: &str) -> i32 {
    let mut cnt = [0usize; 26]; for b in s.bytes() { cnt[(b - b'a') as usize] += 1; } let mut used = vec![false; s.len() + 1]; let mut del = 0; for &c in &cnt { let mut f = c; while f > 0 && used[f] { f -= 1; del += 1; } if f > 0 { used[f] = true; } } del
}
```
