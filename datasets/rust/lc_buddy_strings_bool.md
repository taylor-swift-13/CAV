# LC Buddy Strings Bool

## Problem

Return true if swapping exactly two letters in `s` can make it equal to `goal`.

## Requirements

- Inputs contain lowercase English letters.

## Source

- Source: LeetCode problem `buddy-strings`.
- URL: https://leetcode.com/problems/buddy-strings/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_buddy_strings_bool(s: &str, goal: &str) -> bool {
    let a = s.as_bytes(); let b = goal.as_bytes(); if a.len() != b.len() { return false; } let mut diff = [0usize; 2]; let mut d = 0usize; let mut cnt = [0; 26]; let mut dup = false; let mut i = 0usize; while i < a.len() { let idx = (a[i] - b'a') as usize; cnt[idx] += 1; if cnt[idx] > 1 { dup = true; } if a[i] != b[i] { if d >= 2 { return false; } diff[d] = i; d += 1; } i += 1; } if d == 0 { dup } else { d == 2 && a[diff[0]] == b[diff[1]] && a[diff[1]] == b[diff[0]] }
}
```
