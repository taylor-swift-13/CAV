# LC Hand Of Straights Bool

## Problem

Return true if the hand can be rearranged into groups of consecutive cards.

## Requirements

- `hand` is a comma-separated list of card values.
- `group_size > 0`.

## Source

- Source: LeetCode problem `hand-of-straights`.
- URL: https://leetcode.com/problems/hand-of-straights/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_hand_of_straights_bool(hand: &str, group_size: i32) -> bool {
    let mut a: Vec<i32> = hand.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); if a.len() as i32 % group_size != 0 { return false; } a.sort(); let mut used = vec![false; a.len()]; let mut i = 0usize; while i < a.len() { if !used[i] { let mut need = a[i]; let mut g = 0; while g < group_size { let mut found = None; let mut j = 0usize; while j < a.len() { if !used[j] && a[j] == need { found = Some(j); break; } j += 1; } if let Some(idx) = found { used[idx] = true; need += 1; } else { return false; } g += 1; } } i += 1; } true
}
```
