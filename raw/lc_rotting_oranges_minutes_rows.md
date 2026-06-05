# LC Rotting Oranges Minutes Rows

## Problem

Return the minimum minutes until no fresh orange remains, or `-1` if impossible.

## Requirements

- Rows are semicolon-separated strings of digits.
- `0` is empty, `1` fresh, and `2` rotten.

## Source

- Source: LeetCode problem `rotting-oranges`.
- URL: https://leetcode.com/problems/rotting-oranges/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_rotting_oranges_minutes_rows(const char *rows) {
    char g[64][64]; int r = 0, cols = 0, i = 0, qx[4096], qy[4096], qt[4096], head = 0, tail = 0, fresh = 0, minutes = 0;
    while (rows[i] != '\0') { int c = 0; while (rows[i] >= '0' && rows[i] <= '2') { g[r][c] = rows[i]; if (g[r][c] == '1') fresh++; if (g[r][c] == '2') { qx[tail] = r; qy[tail] = c; qt[tail] = 0; tail++; } c++; i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; while (head < tail) { int x = qx[head], y = qy[head], t = qt[head++]; if (t > minutes) minutes = t; for (int d = 0; d < 4; d++) { int nx = x + dx[d], ny = y + dy[d]; if (nx >= 0 && nx < r && ny >= 0 && ny < cols && g[nx][ny] == '1') { g[nx][ny] = '2'; fresh--; qx[tail] = nx; qy[tail] = ny; qt[tail] = t + 1; tail++; } } } return fresh == 0 ? minutes : -1;
}
```
