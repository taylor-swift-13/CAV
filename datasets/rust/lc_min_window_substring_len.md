# LC Minimum Window Substring Length

## Problem

Return the length of the shortest substring of `s` containing all characters of `t`, or `0` if none exists.

## Requirements

- Inputs are ASCII.
- Character multiplicity in `t` matters.

## Source

- Source: LeetCode problem `minimum-window-substring`.
- URL: https://leetcode.com/problems/minimum-window-substring/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_window_substring_len(s: &str, t: &str) -> i32 {
    let sb = s.as_bytes(); let tb = t.as_bytes(); let mut need = [0i32; 128]; let mut have = [0i32; 128]; let mut required = 0; for &ch in tb { let i = ch as usize; if need[i] == 0 { required += 1; } need[i] += 1; } let mut formed = 0; let mut left = 0usize; let mut best = 1000000; let mut right = 0usize; while right < sb.len() { let ch = sb[right] as usize; have[ch] += 1; if need[ch] > 0 && have[ch] == need[ch] { formed += 1; } while formed == required { let len = (right - left + 1) as i32; if len < best { best = len; } let lc = sb[left] as usize; left += 1; if need[lc] > 0 && have[lc] == need[lc] { formed -= 1; } have[lc] -= 1; } right += 1; } if best == 1000000 { 0 } else { best }
}
```
