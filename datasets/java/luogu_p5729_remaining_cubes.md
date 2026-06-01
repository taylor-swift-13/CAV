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

```java
class LuoguP5729RemainingCubes {
    public static int luogu_p5729_remaining_cubes(int w, int x, int h, String cuts) {
        boolean[][][] used = new boolean[w + 1][x + 1][h + 1]; if (!cuts.isEmpty()) for (String cut : cuts.split(";")) { String[] p = cut.split(","); int[] v = new int[6]; for (int i = 0; i < 6; i++) v[i] = Integer.parseInt(p[i]); for (int a = v[0]; a <= v[3]; a++) for (int b = v[1]; b <= v[4]; b++) for (int c = v[2]; c <= v[5]; c++) used[a][b][c] = true; }
        int left = 0; for (int a = 1; a <= w; a++) for (int b = 1; b <= x; b++) for (int c = 1; c <= h; c++) if (!used[a][b][c]) left++; return left;
    }
}
```
