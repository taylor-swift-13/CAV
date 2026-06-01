# LC Knight Dialer Count

## Problem

Return how many distinct phone numbers of length `n` a chess knight can dial, modulo `1_000_000_007`.

## Requirements

- The keypad graph is the standard LeetCode knight dialer keypad.

## Source

- Source: LeetCode problem `knight-dialer`.
- URL: https://leetcode.com/problems/knight-dialer/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_knight_dialer_count(int n) {
    int moves[10][3] = {{4,6,-1},{6,8,-1},{7,9,-1},{4,8,-1},{0,3,9},{-1,-1,-1},{0,1,7},{2,6,-1},{1,3,-1},{2,4,-1}}; long long dp[10], next[10], mod = 1000000007LL; for (int i = 0; i < 10; i++) dp[i] = 1; for (int step = 1; step < n; step++) { for (int i = 0; i < 10; i++) next[i] = 0; for (int i = 0; i < 10; i++) for (int k = 0; k < 3; k++) if (moves[i][k] >= 0) next[moves[i][k]] = (next[moves[i][k]] + dp[i]) % mod; for (int i = 0; i < 10; i++) dp[i] = next[i]; } long long ans = 0; for (int i = 0; i < 10; i++) ans = (ans + dp[i]) % mod; return (int)ans;
}
```
