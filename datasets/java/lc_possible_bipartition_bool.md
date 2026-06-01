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

```java
class LcPossibleBipartitionBool {
    public static boolean lc_possible_bipartition_bool(int n, String dislikes) {
        boolean[][] g = new boolean[n + 1][n + 1]; for (String row : dislikes.split(";")) { String[] p = row.split(","); int a = Integer.parseInt(p[0]), b = Integer.parseInt(p[1]); g[a][b] = true; g[b][a] = true; } int[] color = new int[n + 1]; java.util.Arrays.fill(color, -1); int[] q = new int[n + 1]; for (int s = 1; s <= n; s++) if (color[s] < 0) { int head = 0, tail = 0; q[tail++] = s; color[s] = 0; while (head < tail) { int v = q[head++]; for (int to = 1; to <= n; to++) if (g[v][to]) { if (color[to] < 0) { color[to] = 1 - color[v]; q[tail++] = to; } else if (color[to] == color[v]) return false; } } } return true;
    }
}
```
