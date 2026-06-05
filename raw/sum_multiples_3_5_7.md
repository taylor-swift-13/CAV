# sum_multiples_3_5_7

## Problem

Return the sum of integers from `1` to `n` that are divisible by `3`, `5`, or `7`.

## Requirements

- `n >= 0`.
- Include numbers divisible by at least one of 3, 5, or 7.
- Each qualifying number contributes once.
- Return `0` when no number qualifies.

## Source

- Source: LeetCode problem `sum-multiples`.
- URL: https://leetcode.com/problems/sum-multiples/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sum_multiples_3_5_7(int n) {
    int sum = 0;
    for (int i = 1; i <= n; i++) if (i % 3 == 0 || i % 5 == 0 || i % 7 == 0) sum += i;
    return sum;
}
```
