# LC Ransom Note Bool

## Problem

Return true if `ransom` can be constructed from letters in `magazine`.

## Requirements

- Inputs contain lowercase English letters.

## Source

- Source: LeetCode problem `ransom-note`.
- URL: https://leetcode.com/problems/ransom-note/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_ransom_note_bool(ransom: &str, magazine: &str) -> bool {
    let mut cnt = [0i32; 26]; for b in magazine.bytes() { cnt[(b - b'a') as usize] += 1; } for b in ransom.bytes() { let i = (b - b'a') as usize; cnt[i] -= 1; if cnt[i] < 0 { return false; } } true
}
```
