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

```c
static int lc_ciw_max, lc_ciw_target, lc_ciw_memo[1 << 20];
static int lc_ciw_dfs(int mask, int total) { if (lc_ciw_memo[mask] != 0) return lc_ciw_memo[mask] == 1; for (int i = 0; i < lc_ciw_max; i++) if ((mask & (1 << i)) == 0) { int pick = i + 1; if (total + pick >= lc_ciw_target || !lc_ciw_dfs(mask | (1 << i), total + pick)) { lc_ciw_memo[mask] = 1; return 1; } } lc_ciw_memo[mask] = -1; return 0; }
int lc_can_i_win_bool(int max_choosable_integer, int desired_total) {
    if (desired_total <= 0) return 1;
    if (max_choosable_integer * (max_choosable_integer + 1) / 2 < desired_total) return 0;
    lc_ciw_max = max_choosable_integer; lc_ciw_target = desired_total; int limit = 1 << max_choosable_integer; for (int i = 0; i < limit; i++) lc_ciw_memo[i] = 0; return lc_ciw_dfs(0, 0);
}
```
