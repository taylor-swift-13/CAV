# LC Number Of Ways Stay Same Place

## Problem

Return how many ways to be at index 0 after exactly `steps` moves.

## Requirements

- At each move, stay, move left, or move right within array bounds.
- Return the count modulo `1_000_000_007`.

## Source

- Source: LeetCode problem `number-of-ways-to-stay-in-the-same-place-after-some-steps`.
- URL: https://leetcode.com/problems/number-of-ways-to-stay-in-the-same-place-after-some-steps/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_num_ways_stay_same_place(int steps, int arr_len) {
    int mod = 1000000007, max_pos = steps < arr_len ? steps : arr_len - 1; int dp[512] = {0}, next[512]; dp[0] = 1; for (int s = 0; s < steps; s++) { for (int i = 0; i <= max_pos; i++) next[i] = 0; for (int i = 0; i <= max_pos; i++) { next[i] = (next[i] + dp[i]) % mod; if (i > 0) next[i - 1] = (next[i - 1] + dp[i]) % mod; if (i < max_pos) next[i + 1] = (next[i + 1] + dp[i]) % mod; } for (int i = 0; i <= max_pos; i++) dp[i] = next[i]; } return dp[0];
}
```
