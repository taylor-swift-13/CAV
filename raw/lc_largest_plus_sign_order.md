# LC Largest Plus Sign Order

## Problem

Return the order of the largest axis-aligned plus sign.

## Requirements

- Mines are encoded as `r,c;...`; use `-` for no mines.
- Grid size is `n x n`.

## Source

- Source: LeetCode problem `order-of-largest-plus-sign`.
- URL: https://leetcode.com/problems/order-of-largest-plus-sign/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_largest_plus_sign_order(int n, const char *mines) {
    int g[64][64]; for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) g[i][j] = 1; int idx = 0; if (mines[0] != '-') while (mines[idx] != '\0') { int r = 0, c = 0; while (mines[idx] >= '0' && mines[idx] <= '9') { r = r * 10 + (mines[idx] - '0'); idx++; } if (mines[idx] == ',') idx++; while (mines[idx] >= '0' && mines[idx] <= '9') { c = c * 10 + (mines[idx] - '0'); idx++; } g[r][c] = 0; if (mines[idx] == ';') idx++; } int best = 0; for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) if (g[x][y]) { int order = 1; while (x - order >= 0 && x + order < n && y - order >= 0 && y + order < n && g[x - order][y] && g[x + order][y] && g[x][y - order] && g[x][y + order]) order++; if (order > best) best = order; } return best;
}
```
