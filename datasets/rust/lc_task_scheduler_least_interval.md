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

```rust
pub fn lc_task_scheduler_least_interval(tasks: &str, n: i32) -> i32 {
    let mut cnt = [0; 26]; let mut max = 0; for b in tasks.bytes() { let i = (b - b'A') as usize; cnt[i] += 1; if cnt[i] > max { max = cnt[i]; } } let mut same = 0; for v in cnt { if v == max { same += 1; } } let frame = (max - 1) * (n + 1) + same; let len = tasks.len() as i32; if frame > len { frame } else { len }
}
```
