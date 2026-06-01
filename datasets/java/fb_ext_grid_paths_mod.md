# FormalBench Grid Paths Mod

## Problem

Return the number of right/down paths from the top-left to bottom-right cell of a `rows` by `cols` grid, modulo `1000000007`.

## Requirements

- `0 <= rows, cols <= 30`.
- Return `0` if either dimension is `0`.
- A `1` by `1` grid has one path.

## Source

- Source: FormalBench problem `FormalBenchHF/base/programs/NcrModP.java`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: local rewrite from SESpec java_flat.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbExtGridPathsMod {
    public static int fb_ext_grid_paths_mod(int rows, int cols) {
        if (rows <= 0 || cols <= 0) return 0;
        int[][] dp = new int[rows][cols];
        for (int i = 0; i < rows; i++) dp[i][0] = 1;
        for (int j = 0; j < cols; j++) dp[0][j] = 1;
        for (int i = 1; i < rows; i++) {
            for (int j = 1; j < cols; j++) dp[i][j] = (dp[i - 1][j] + dp[i][j - 1]) % 1000000007;
        }
        return dp[rows - 1][cols - 1];
    }
}
```
