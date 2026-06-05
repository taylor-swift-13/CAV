# LC Redundant Connection Edge Code

## Problem

Return the redundant undirected edge encoded as `u * 1000 + v`.

## Requirements

- `edges` is semicolon-separated `u,v` pairs.
- Return the last edge whose addition creates a cycle.

## Source

- Source: LeetCode problem `redundant-connection`.
- URL: https://leetcode.com/problems/redundant-connection/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
static int lc_rc_find(int *parent, int x) { while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; }
int lc_redundant_connection_edge_code(const char *edges) {
    int parent[1001]; for (int i = 0; i <= 1000; i++) parent[i] = i; int i = 0, ans = 0; while (edges[i] != '\0') { int u = 0, v = 0; while (edges[i] >= '0' && edges[i] <= '9') { u = u * 10 + edges[i] - '0'; i++; } if (edges[i] == ',') i++; while (edges[i] >= '0' && edges[i] <= '9') { v = v * 10 + edges[i] - '0'; i++; } int ru = lc_rc_find(parent, u), rv = lc_rc_find(parent, v); if (ru == rv) ans = u * 1000 + v; else parent[ru] = rv; if (edges[i] == ';') i++; } return ans;
}
```
