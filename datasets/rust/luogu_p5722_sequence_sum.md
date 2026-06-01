# Luogu P5722 Sequence Sum

## Problem

Return the sum `1 + 2 + ... + n`.

## Requirements

- `n >= 1`.
- The result fits in signed 32-bit integer range.

## Source

- Source: Luogu problem `P5722`.
- URL: https://www.luogu.com.cn/problem/P5722
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5722_sequence_sum(n: i32) -> i32 {
    n * (n + 1) / 2
}
```
