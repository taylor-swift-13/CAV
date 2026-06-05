# LC Network Connected Operations

## Problem

Return the minimum cable moves needed to connect all computers, or `-1` if impossible.

## Requirements

- Connections are encoded as `u,v;...`.
- Computers are numbered from `0` to `n-1`.

## Source

- Source: LeetCode problem `number-of-operations-to-make-network-connected`.
- URL: https://leetcode.com/problems/number-of-operations-to-make-network-connected/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_make_connected_ops(int n, const char *connections) {
    int g[128][128] = {{0}}, edges = 0, i = 0; while (connections[i] != '\0') { int a = 0, b = 0; while (connections[i] >= '0' && connections[i] <= '9') { a = a * 10 + (connections[i] - '0'); i++; } if (connections[i] == ',') i++; while (connections[i] >= '0' && connections[i] <= '9') { b = b * 10 + (connections[i] - '0'); i++; } g[a][b] = 1; g[b][a] = 1; edges++; if (connections[i] == ';') i++; } if (edges < n - 1) return -1; int seen[128] = {0}, comps = 0, q[128]; for (int s = 0; s < n; s++) if (!seen[s]) { comps++; int head = 0, tail = 0; q[tail++] = s; seen[s] = 1; while (head < tail) { int v = q[head++]; for (int to = 0; to < n; to++) if (g[v][to] && !seen[to]) { seen[to] = 1; q[tail++] = to; } } } return comps - 1;
}
```
