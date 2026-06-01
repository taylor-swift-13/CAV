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

```c
int lc_course_schedule_can_finish(int num_courses, const char *prereqs) {
    int g[128][128] = {{0}}, indeg[128] = {0}, i = 0;
    while (prereqs[i] != '\0') { int a = 0, b = 0; while (prereqs[i] >= '0' && prereqs[i] <= '9') { a = a * 10 + prereqs[i] - '0'; i++; } if (prereqs[i] == ',') i++; while (prereqs[i] >= '0' && prereqs[i] <= '9') { b = b * 10 + prereqs[i] - '0'; i++; } if (!g[b][a]) { g[b][a] = 1; indeg[a]++; } if (prereqs[i] == ';') i++; }
    int q[128], head = 0, tail = 0, seen = 0; for (int c = 0; c < num_courses; c++) if (indeg[c] == 0) q[tail++] = c;
    while (head < tail) { int v = q[head++]; seen++; for (int to = 0; to < num_courses; to++) if (g[v][to] && --indeg[to] == 0) q[tail++] = to; }
    return seen == num_courses;
}
```
