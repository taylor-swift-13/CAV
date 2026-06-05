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

```java
class LcNumWaysStaySamePlace {
    public static int lc_num_ways_stay_same_place(int steps, int arr_len) {
        int mod = 1000000007, max = Math.min(steps, arr_len - 1); int[] dp = new int[max + 1]; dp[0] = 1; for (int s = 0; s < steps; s++) { int[] next = new int[max + 1]; for (int i = 0; i <= max; i++) { next[i] = (next[i] + dp[i]) % mod; if (i > 0) next[i - 1] = (next[i - 1] + dp[i]) % mod; if (i < max) next[i + 1] = (next[i + 1] + dp[i]) % mod; } dp = next; } return dp[0];
    }
}
```
