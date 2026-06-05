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

```c
int lc_find_town_judge(int n, const char *trust) {
    int score[128] = {0}, i = 0; while (trust[i] != '\0') { int a = 0, b = 0; while (trust[i] >= '0' && trust[i] <= '9') { a = a * 10 + trust[i] - '0'; i++; } if (trust[i] == ',') i++; while (trust[i] >= '0' && trust[i] <= '9') { b = b * 10 + trust[i] - '0'; i++; } score[a]--; score[b]++; if (trust[i] == ';') i++; } for (int person = 1; person <= n; person++) if (score[person] == n - 1) return person; return -1;
}
```
