# LC Possible Bipartition Bool

## Problem

Return true if people can be split into two groups so no dislike pair is inside a group.

## Requirements

- Dislike pairs are encoded as `a,b;...`.
- People are numbered from `1` to `n`.

## Source

- Source: LeetCode problem `possible-bipartition`.
- URL: https://leetcode.com/problems/possible-bipartition/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_possible_bipartition_bool(int n, const char *dislikes) {
    int g[128][128] = {{0}}, i = 0; while (dislikes[i] != '\0') { int a = 0, b = 0; while (dislikes[i] >= '0' && dislikes[i] <= '9') { a = a * 10 + (dislikes[i] - '0'); i++; } if (dislikes[i] == ',') i++; while (dislikes[i] >= '0' && dislikes[i] <= '9') { b = b * 10 + (dislikes[i] - '0'); i++; } g[a][b] = 1; g[b][a] = 1; if (dislikes[i] == ';') i++; }
    int color[128]; for (int x = 1; x <= n; x++) color[x] = -1; int q[128]; for (int s = 1; s <= n; s++) if (color[s] < 0) { int head = 0, tail = 0; q[tail] = s; tail++; color[s] = 0; while (head < tail) { int v = q[head++]; for (int to = 1; to <= n; to++) if (g[v][to]) { if (color[to] < 0) { color[to] = 1 - color[v]; q[tail] = to; tail++; } else if (color[to] == color[v]) return 0; } } } return 1;
}
```
