# LC Robot Return To Origin Bool

## Problem

Return true if robot moves return to coordinate `(0,0)`.

## Requirements

- `moves` contains only `U`, `D`, `L`, and `R`.

## Source

- Source: LeetCode problem `robot-return-to-origin`.
- URL: https://leetcode.com/problems/robot-return-to-origin/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_robot_return_origin_bool(moves: &str) -> bool {
    let mut x = 0; let mut y = 0; for ch in moves.bytes() { if ch == b'U' { y += 1; } else if ch == b'D' { y -= 1; } else if ch == b'L' { x -= 1; } else if ch == b'R' { x += 1; } } x == 0 && y == 0
}
```
