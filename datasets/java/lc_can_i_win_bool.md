# LC Can I Win Bool

## Problem

Return true if the first player can force a win.

## Requirements

- Players alternately choose unused integers from `1..max_choosable_integer`.
- The player who reaches or exceeds `desired_total` wins.

## Source

- Source: LeetCode problem `can-i-win`.
- URL: https://leetcode.com/problems/can-i-win/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcCanIWinBool {
    static int max, target; static int[] memo;
    static boolean dfs(int mask, int total) { if (memo[mask] != 0) return memo[mask] == 1; for (int i = 0; i < max; i++) if ((mask & (1 << i)) == 0) { int pick = i + 1; if (total + pick >= target || !dfs(mask | (1 << i), total + pick)) { memo[mask] = 1; return true; } } memo[mask] = -1; return false; }
    public static boolean lc_can_i_win_bool(int max_choosable_integer, int desired_total) {
        if (desired_total <= 0) return true; if (max_choosable_integer * (max_choosable_integer + 1) / 2 < desired_total) return false; max = max_choosable_integer; target = desired_total; memo = new int[1 << max]; return dfs(0, 0);
    }
}
```
