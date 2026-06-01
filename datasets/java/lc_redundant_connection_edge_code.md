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

```java
class LcRedundantConnectionEdgeCode {
    static int find(int[] parent, int x) { while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; }
    public static int lc_redundant_connection_edge_code(String edges) {
        int[] parent = new int[1001]; for (int i = 0; i < parent.length; i++) parent[i] = i; int ans = 0; for (String e : edges.split(";")) { String[] p = e.split(","); int u = Integer.parseInt(p[0]), v = Integer.parseInt(p[1]); int ru = find(parent, u), rv = find(parent, v); if (ru == rv) ans = u * 1000 + v; else parent[ru] = rv; } return ans;
    }
}
```
