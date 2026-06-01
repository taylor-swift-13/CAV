# LC Course Schedule Can Finish

## Problem

Return true if all courses can be completed from prerequisite pairs.

## Requirements

- Pairs are encoded as `course,prerequisite;...`.
- The empty prerequisite string has no edges.
- `num_courses <= 128`.

## Source

- Source: LeetCode problem `course-schedule`.
- URL: https://leetcode.com/problems/course-schedule/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_course_schedule_can_finish(num_courses: i32, prereqs: &str) -> bool {
    let n = num_courses as usize; let mut g = vec![vec![false; n]; n]; let mut indeg = vec![0; n];
    if !prereqs.is_empty() { for e in prereqs.split(';') { let p: Vec<usize> = e.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); if !g[p[1]][p[0]] { g[p[1]][p[0]] = true; indeg[p[0]] += 1; } } }
    let mut q: Vec<usize> = Vec::new(); let mut i = 0usize; while i < n { if indeg[i] == 0 { q.push(i); } i += 1; } let mut head = 0usize; let mut seen = 0usize;
    while head < q.len() { let v = q[head]; head += 1; seen += 1; let mut to = 0usize; while to < n { if g[v][to] { indeg[to] -= 1; if indeg[to] == 0 { q.push(to); } } to += 1; } } seen == n
}
```
