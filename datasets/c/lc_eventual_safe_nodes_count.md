# LC Eventual Safe Nodes Count

## Problem

Return how many nodes are eventually safe in a directed graph.

## Requirements

- `edges` is semicolon-separated `from,to` pairs.
- Nodes with no outgoing edges are terminal and safe.

## Source

- Source: LeetCode problem `find-eventual-safe-states`.
- URL: https://leetcode.com/problems/find-eventual-safe-states/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_eventual_safe_nodes_count(int n, const char *edges) {
    int rev[128][128] = {{0}}, revn[128] = {0}, out[128] = {0}, i = 0; while (edges[i] != '\0') { int a = 0, b = 0; while (edges[i] >= '0' && edges[i] <= '9') { a = a * 10 + edges[i] - '0'; i++; } if (edges[i] == ',') i++; while (edges[i] >= '0' && edges[i] <= '9') { b = b * 10 + edges[i] - '0'; i++; } rev[b][revn[b]++] = a; out[a]++; if (edges[i] == ';') i++; } int q[128], h = 0, t = 0; for (int v = 0; v < n; v++) if (out[v] == 0) q[t++] = v; while (h < t) { int v = q[h++]; for (int k = 0; k < revn[v]; k++) if (--out[rev[v][k]] == 0) q[t++] = rev[v][k]; } return t;
}
```
