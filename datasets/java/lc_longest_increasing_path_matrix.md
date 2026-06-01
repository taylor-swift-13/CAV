# LC Longest Increasing Path Matrix

## Problem

Return the length of the longest strictly increasing 4-directional path in a matrix.

## Requirements

- Rows are semicolon-separated comma lists of signed integers.

## Source

- Source: LeetCode problem `longest-increasing-path-in-a-matrix`.
- URL: https://leetcode.com/problems/longest-increasing-path-in-a-matrix/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLongestIncreasingPathMatrix {
    static int dfs(int x, int y, int[][] a, int[][] memo) { if (memo[x][y] != 0) return memo[x][y]; int best = 1; int[] dx = {1,-1,0,0}, dy = {0,0,1,-1}; for (int k = 0; k < 4; k++) { int nx = x + dx[k], ny = y + dy[k]; if (nx >= 0 && nx < a.length && ny >= 0 && ny < a[0].length && a[nx][ny] > a[x][y]) best = Math.max(best, 1 + dfs(nx, ny, a, memo)); } return memo[x][y] = best; }
    public static int lc_longest_increasing_path_matrix(String rows) {
        String[] rs = rows.split(";"); int[][] a = new int[rs.length][]; for (int i = 0; i < rs.length; i++) { String[] p = rs[i].split(","); a[i] = new int[p.length]; for (int j = 0; j < p.length; j++) a[i][j] = Integer.parseInt(p[j]); } int[][] memo = new int[a.length][a[0].length]; int ans = 0; for (int i = 0; i < a.length; i++) for (int j = 0; j < a[0].length; j++) ans = Math.max(ans, dfs(i, j, a, memo)); return ans;
    }
}
```
