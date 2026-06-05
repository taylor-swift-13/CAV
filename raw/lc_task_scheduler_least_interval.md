# LC Task Scheduler Least Interval

## Problem

Return the minimum intervals needed to execute tasks with cooldown `n`.

## Requirements

- `tasks` is a string of uppercase task letters.
- `n >= 0`.

## Source

- Source: LeetCode problem `task-scheduler`.
- URL: https://leetcode.com/problems/task-scheduler/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_task_scheduler_least_interval(const char *tasks, int n) {
    int cnt[26] = {0}, len = 0, max = 0, same = 0; for (int i = 0; tasks[i] != '\0'; i++) { int v = ++cnt[tasks[i] - 'A']; len++; if (v > max) max = v; }
    for (int i = 0; i < 26; i++) if (cnt[i] == max) same++;
    int frame = (max - 1) * (n + 1) + same;
    return frame > len ? frame : len;
}
```
