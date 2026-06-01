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

```java
class LcCourseScheduleCanFinish {
    public static boolean lc_course_schedule_can_finish(int num_courses, String prereqs) {
        boolean[][] g = new boolean[num_courses][num_courses]; int[] indeg = new int[num_courses];
        if (!prereqs.isEmpty()) for (String e : prereqs.split(";")) { String[] p = e.split(","); int a = Integer.parseInt(p[0]), b = Integer.parseInt(p[1]); if (!g[b][a]) { g[b][a] = true; indeg[a]++; } }
        int[] q = new int[num_courses]; int head = 0, tail = 0, seen = 0; for (int i = 0; i < num_courses; i++) if (indeg[i] == 0) q[tail++] = i;
        while (head < tail) { int v = q[head++]; seen++; for (int to = 0; to < num_courses; to++) if (g[v][to] && --indeg[to] == 0) q[tail++] = to; } return seen == num_courses;
    }
}
```
