# Luogu P5729 Remaining Cubes

## Problem

Return how many unit cubes remain after deleting inclusive cuboids from a `w*x*h` block.

## Requirements

- Cuboids are encoded as `x1,y1,z1,x2,y2,z2;...` using one-based inclusive coordinates.
- The empty cuboid string deletes nothing.
- `w`, `x`, and `h` are at most 20 in supplied tests.

## Source

- Source: Luogu problem `P5729`.
- URL: https://www.luogu.com.cn/problem/P5729
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5729_remaining_cubes(int w, int x, int h, const char *cuts) {
    int used[21][21][21] = {{{0}}}, i = 0;
    while (cuts[i] != '\0') { int v[6]; for (int k = 0; k < 6; k++) { v[k] = 0; while (cuts[i] >= '0' && cuts[i] <= '9') { v[k] = v[k] * 10 + (cuts[i] - '0'); i++; } if (cuts[i] == ',') i++; } for (int a = v[0]; a <= v[3]; a++) for (int b = v[1]; b <= v[4]; b++) for (int c = v[2]; c <= v[5]; c++) used[a][b][c] = 1; if (cuts[i] == ';') i++; }
    int left = 0; for (int a = 1; a <= w; a++) for (int b = 1; b <= x; b++) for (int c = 1; c <= h; c++) if (!used[a][b][c]) left++; return left;
}
```
