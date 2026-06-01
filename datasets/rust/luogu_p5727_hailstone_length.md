# Luogu P5727 Hailstone Length

## Problem

Return how many numbers appear in the Collatz sequence from `n` down to `1`, including both endpoints.

## Requirements

- `n >= 1`.
- Use `n/2` for even values and `3*n+1` for odd values.

## Source

- Source: Luogu problem `P5727`.
- URL: https://www.luogu.com.cn/problem/P5727
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5727_hailstone_length(mut n: i32) -> i32 {
    let mut len = 1; while n != 1 { if n % 2 == 0 { n /= 2; } else { n = 3 * n + 1; } len += 1; } len
}
```
