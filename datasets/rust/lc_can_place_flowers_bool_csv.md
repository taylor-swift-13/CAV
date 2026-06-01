# LC Can Place Flowers Bool CSV

## Problem

Return true if `n` new flowers can be planted without adjacent flowers.

## Requirements

- `bed` is a comma-separated list of `0` and `1`.
- Existing flowers are not adjacent.

## Source

- Source: LeetCode problem `can-place-flowers`.
- URL: https://leetcode.com/problems/can-place-flowers/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_can_place_flowers_bool_csv(bed: &str, mut n: i32) -> bool {
    let mut a: Vec<i32> = bed.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut i = 0usize; while i < a.len() && n > 0 { if a[i] == 0 && (i == 0 || a[i - 1] == 0) && (i == a.len() - 1 || a[i + 1] == 0) { a[i] = 1; n -= 1; } i += 1; } n <= 0
}
```
