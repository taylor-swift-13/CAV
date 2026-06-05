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

```c
int luogu_p5739_factorial(int n) {
    int ans = 1; for (int i = 2; i <= n; i++) ans *= i; return ans;
}
```
