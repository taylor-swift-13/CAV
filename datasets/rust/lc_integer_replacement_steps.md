# LC Integer Replacement Steps

## Problem

Return the minimum number of replacements needed to reduce `n` to `1`.

## Requirements

- If `n` is even divide by 2; if odd replace by `n+1` or `n-1`.

## Source

- Source: LeetCode problem `integer-replacement`.
- URL: https://leetcode.com/problems/integer-replacement/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_integer_replacement_steps(n: i32) -> i32 {
    let mut x = n as i64; let mut steps = 0; while x != 1 { if x % 2 == 0 { x /= 2; } else if x == 3 || x % 4 == 1 { x -= 1; } else { x += 1; } steps += 1; } steps
}
```
