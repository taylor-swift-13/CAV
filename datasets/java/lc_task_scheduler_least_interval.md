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

```java
class LcTaskSchedulerLeastInterval {
    public static int lc_task_scheduler_least_interval(String tasks, int n) {
        int[] cnt = new int[26]; int max = 0; for (int i = 0; i < tasks.length(); i++) { int v = ++cnt[tasks.charAt(i) - 'A']; if (v > max) max = v; } int same = 0; for (int v : cnt) if (v == max) same++; int frame = (max - 1) * (n + 1) + same; return Math.max(frame, tasks.length());
    }
}
```
