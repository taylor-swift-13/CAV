# Luogu P5736 Prime Count CSV

## Problem

Return how many comma-separated integers are prime.

## Requirements

- The empty string represents an empty list.
- Values are nonnegative.

## Source

- Source: Luogu problem `P5736`.
- URL: https://www.luogu.com.cn/problem/P5736
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5736_prime_count_csv(const char *nums) {
    if (nums[0] == '\0') return 0;
    int count = 0, i = 0;
    while (nums[i] != '\0') { int x = 0; while (nums[i] >= '0' && nums[i] <= '9') { x = x * 10 + nums[i] - '0'; i++; } int prime = x >= 2; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = 0; if (prime) count++; if (nums[i] == ',') i++; }
    return count;
}
```
