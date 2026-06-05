# LC IPO Max Capital CSV

## Problem

Return maximized capital after selecting at most `k` projects.

## Requirements

- `profits` and `capital` are comma-separated arrays of equal length.
- Each project can be selected at most once.

## Source

- Source: LeetCode problem `ipo`.
- URL: https://leetcode.com/problems/ipo/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_ipo_max_capital_csv(int k, int w, const char *profits, const char *capital) {
    int p[512], c[512], n = 0, i = 0; while (profits[i] != '\0') { int v = 0; while (profits[i] >= '0' && profits[i] <= '9') { v = v * 10 + (profits[i] - '0'); i++; } p[n] = v; n++; if (profits[i] == ',') i++; } i = 0; int m = 0; while (capital[i] != '\0') { int v = 0; while (capital[i] >= '0' && capital[i] <= '9') { v = v * 10 + (capital[i] - '0'); i++; } c[m] = v; m++; if (capital[i] == ',') i++; }
    int used[512] = {0}; for (int step = 0; step < k; step++) { int best = -1; for (int x = 0; x < n; x++) if (!used[x] && c[x] <= w && (best < 0 || p[x] > p[best])) best = x; if (best < 0) break; used[best] = 1; w += p[best]; } return w;
}
```
