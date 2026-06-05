# LC Out Of Boundary Paths Count

## Problem

Return how many paths move out of grid boundary within at most `max_move` moves.

## Requirements

- Start at `(start_row,start_column)` in an `m x n` grid.
- Return the count modulo `1_000_000_007`.

## Source

- Source: LeetCode problem `out-of-boundary-paths`.
- URL: https://leetcode.com/problems/out-of-boundary-paths/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcOutBoundaryPathsCount {
    public static int lc_out_boundary_paths_count(int m, int n, int max_move, int start_row, int start_column) {
        int mod = 1000000007; int[][] dp = new int[m][n]; dp[start_row][start_column] = 1; long ans = 0; int[] dx = {1,-1,0,0}, dy = {0,0,1,-1}; for (int move = 0; move < max_move; move++) { int[][] next = new int[m][n]; for (int i = 0; i < m; i++) for (int j = 0; j < n; j++) if (dp[i][j] != 0) for (int d = 0; d < 4; d++) { int ni = i + dx[d], nj = j + dy[d]; if (ni < 0 || ni >= m || nj < 0 || nj >= n) ans = (ans + dp[i][j]) % mod; else next[ni][nj] = (next[ni][nj] + dp[i][j]) % mod; } dp = next; } return (int)ans;
    }
}
```
