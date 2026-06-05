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

```java
class LcKnightDialerCount {
    public static int lc_knight_dialer_count(int n) {
        int[][] moves = {{4,6},{6,8},{7,9},{4,8},{0,3,9},{},{0,1,7},{2,6},{1,3},{2,4}}; long mod = 1000000007L; long[] dp = new long[10]; java.util.Arrays.fill(dp, 1); for (int step = 1; step < n; step++) { long[] next = new long[10]; for (int i = 0; i < 10; i++) for (int to : moves[i]) next[to] = (next[to] + dp[i]) % mod; dp = next; } long ans = 0; for (long v : dp) ans = (ans + v) % mod; return (int)ans;
    }
}
```
