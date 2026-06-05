# LC Find Town Judge

## Problem

Return the label of the town judge, or `-1` if no judge exists.

## Requirements

- `trust` is semicolon-separated `a,b` pairs.
- People are labeled from `1` to `n`.

## Source

- Source: LeetCode problem `find-the-town-judge`.
- URL: https://leetcode.com/problems/find-the-town-judge/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcFindTownJudge {
    public static int lc_find_town_judge(int n, String trust) {
        int[] score = new int[n + 1]; for (String pair : trust.split(";")) { String[] p = pair.split(","); score[Integer.parseInt(p[0])]--; score[Integer.parseInt(p[1])]++; } for (int i = 1; i <= n; i++) if (score[i] == n - 1) return i; return -1;
    }
}
```
