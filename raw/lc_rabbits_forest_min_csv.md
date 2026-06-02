# LC Rabbits In Forest Minimum CSV

## Problem

Return the minimum number of rabbits consistent with the answers.

## Requirements

- `answers` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `rabbits-in-forest`.
- URL: https://leetcode.com/problems/rabbits-in-forest/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_rabbits_forest_min_csv(const char *answers) {
    int a[512], n = 0, i = 0; while (answers[i] != '\0') { int v = 0; while (answers[i] >= '0' && answers[i] <= '9') { v = v * 10 + answers[i] - '0'; i++; } a[n++] = v; if (answers[i] == ',') i++; } int total = 0; for (int x = 0; x < n; x++) { int seen = 0; for (int y = 0; y < x; y++) if (a[y] == a[x]) seen = 1; if (!seen) { int cnt = 0; for (int y = 0; y < n; y++) if (a[y] == a[x]) cnt++; int group = a[x] + 1; total += ((cnt + group - 1) / group) * group; } } return total;
}
```
