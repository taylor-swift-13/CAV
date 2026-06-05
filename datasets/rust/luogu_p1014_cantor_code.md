# Luogu P1014 Cantor Code

## Problem

Return the Cantor-table fraction at position `n` encoded as `numerator * 1000 + denominator`.

## Requirements

- Use the zigzag diagonal order from Luogu P1014.
- `n` is positive.

## Source

- Source: Luogu problem `P1014`.
- URL: https://www.luogu.com.cn/problem/P1014
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p1014_cantor_code(n: i32) -> i32 {
    let mut diag = 1; let mut used = 0; while used + diag < n { used += diag; diag += 1; } let offset = n - used; let (num, den) = if diag % 2 == 0 { (offset, diag - offset + 1) } else { (diag - offset + 1, offset) }; num * 1000 + den
}
```
