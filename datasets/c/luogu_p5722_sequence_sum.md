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

```c
int luogu_p5722_sequence_sum(int n) {
    return n * (n + 1) / 2;
}
```
