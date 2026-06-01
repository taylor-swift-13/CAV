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

```java
class LuoguP5727HailstoneLength {
    public static int luogu_p5727_hailstone_length(int n) {
        int len = 1; while (n != 1) { if (n % 2 == 0) n /= 2; else n = 3 * n + 1; len++; } return len;
    }
}
```
