# Luogu P5728 Similar Triples Count

## Problem

Count pairs of students whose three subject scores differ by at most 5 each and total scores differ by at most 10.

## Requirements

- Rows are encoded as `a,b,c;a,b,c;...`.
- The empty string returns `0`.

## Source

- Source: Luogu problem `P5728`.
- URL: https://www.luogu.com.cn/problem/P5728
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5728_similar_triples_count(const char *rows) {
    if (rows[0] == '\0') return 0;
    int a[64][3], n = 0, i = 0;
    while (rows[i] != '\0') { for (int k = 0; k < 3; k++) { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[n][k] = v; if (rows[i] == ',') i++; } n++; if (rows[i] == ';') i++; }
    int count = 0;
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) { int ok = 1; for (int k = 0; k < 3; k++) { int d = a[x][k] - a[y][k]; if (d < 0) d = -d; if (d > 5) ok = 0; } int tx = a[x][0] + a[x][1] + a[x][2], ty = a[y][0] + a[y][1] + a[y][2], td = tx - ty; if (td < 0) td = -td; if (ok && td <= 10) count++; }
    return count;
}
```
