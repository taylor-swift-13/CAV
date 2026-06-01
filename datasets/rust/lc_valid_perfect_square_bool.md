# LC Valid Perfect Square Bool

## Problem

Return true if `num` is a perfect square.

## Requirements

- `num > 0`.
- Use integer arithmetic only.

## Source

- Source: LeetCode problem `valid-perfect-square`.
- URL: https://leetcode.com/problems/valid-perfect-square/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_valid_perfect_square_bool(num: i32) -> bool {
    let mut l: i64 = 1; let mut r: i64 = num as i64; while l <= r { let m = (l + r) / 2; let sq = m * m; if sq == num as i64 { return true; } if sq < num as i64 { l = m + 1; } else { r = m - 1; } } false
}
```
