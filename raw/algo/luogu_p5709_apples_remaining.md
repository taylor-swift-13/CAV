# Luogu P5709 Apples Remaining

## Problem

Return how many apples remain after worms eat one apple every `t` seconds for `s` seconds.

## Requirements

- `m >= 0`, `t > 0`, and `s >= 0`.
- A partially eaten apple counts as eaten.

## Source

- Source: Luogu problem `P5709`.
- URL: https://www.luogu.com.cn/problem/P5709
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5709_apples_remaining(int m, int t, int s) {
    int eaten = (s + t - 1) / t;
    int left = m - eaten;
    return left > 0 ? left : 0;
}
```
