# LC Dice Rolls With Target Sum

## Problem

Return how many ways `n` dice with faces `1..k` sum to `target`, modulo `1_000_000_007`.

## Requirements

- `n`, `k`, and `target` are nonnegative and small in supplied tests.

## Source

- Source: LeetCode problem `number-of-dice-rolls-with-target-sum`.
- URL: https://leetcode.com/problems/number-of-dice-rolls-with-target-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_num_dice_rolls_target(int n, int k, int target) {
    int mod = 1000000007; long long dp[1001] = {0}; dp[0] = 1; for (int d = 0; d < n; d++) { long long next[1001] = {0}; for (int s = 0; s <= target; s++) if (dp[s]) for (int face = 1; face <= k && s + face <= target; face++) next[s + face] = (next[s + face] + dp[s]) % mod; for (int s = 0; s <= target; s++) dp[s] = next[s]; } return (int)dp[target];
}
```
