# Luogu P5739 Factorial

## Problem

Return `n!`.

## Requirements

- `0 <= n <= 12`.
- The result fits in signed 32-bit integer range.

## Source

- Source: Luogu problem `P5739`.
- URL: https://www.luogu.com.cn/problem/P5739
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5739_factorial(n: i32) -> i32 {
    let mut ans = 1; let mut i = 2; while i <= n { ans *= i; i += 1; } ans
}
```
