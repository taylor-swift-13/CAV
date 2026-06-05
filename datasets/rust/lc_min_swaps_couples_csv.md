# LC Couples Holding Hands Min Swaps CSV

## Problem

Return the minimum adjacent-seat swaps needed so every couple sits together.

## Requirements

- `row` is a comma-separated seating arrangement.
- Couples are `(0,1)`, `(2,3)`, and so on.

## Source

- Source: LeetCode problem `couples-holding-hands`.
- URL: https://leetcode.com/problems/couples-holding-hands/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_swaps_couples_csv(row: &str) -> i32 {
    let mut a: Vec<usize> = row.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); let mut pos = vec![0usize; a.len()]; let mut i = 0usize; while i < a.len() { pos[a[i]] = i; i += 1; } let mut swaps = 0; let mut seat = 0usize; while seat < a.len() { let mate = a[seat] ^ 1; if a[seat + 1] != mate { let mpos = pos[mate]; let other = a[seat + 1]; a[mpos] = other; pos[other] = mpos; a[seat + 1] = mate; pos[mate] = seat + 1; swaps += 1; } seat += 2; } swaps
}
```
