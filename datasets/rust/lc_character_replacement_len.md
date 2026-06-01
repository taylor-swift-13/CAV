# LC Longest Repeating Character Replacement Length

## Problem

Return the longest substring length that can be made of one repeated character after at most `k` replacements.

## Requirements

- `s` contains uppercase English letters.
- `k >= 0`.

## Source

- Source: LeetCode problem `longest-repeating-character-replacement`.
- URL: https://leetcode.com/problems/longest-repeating-character-replacement/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_character_replacement_len(s: &str, k: i32) -> i32 {
    let b = s.as_bytes(); let mut cnt = [0i32; 26]; let mut left = 0usize; let mut maxc = 0; let mut best = 0; let mut right = 0usize; while right < b.len() { let idx = (b[right] - b'A') as usize; cnt[idx] += 1; if cnt[idx] > maxc { maxc = cnt[idx]; } while right as i32 - left as i32 + 1 - maxc > k { cnt[(b[left] - b'A') as usize] -= 1; left += 1; } let len = right as i32 - left as i32 + 1; if len > best { best = len; } right += 1; } best
}
```
