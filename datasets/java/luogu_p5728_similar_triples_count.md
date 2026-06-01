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

```java
class LuoguP5728SimilarTriplesCount {
    public static int luogu_p5728_similar_triples_count(String rows) {
        if (rows.isEmpty()) return 0;
        String[] rs = rows.split(";"); int[][] a = new int[rs.length][3];
        for (int i = 0; i < rs.length; i++) { String[] p = rs[i].split(","); for (int k = 0; k < 3; k++) a[i][k] = Integer.parseInt(p[k]); }
        int count = 0;
        for (int x = 0; x < a.length; x++) for (int y = x + 1; y < a.length; y++) { boolean ok = true; for (int k = 0; k < 3; k++) if (Math.abs(a[x][k] - a[y][k]) > 5) ok = false; int tx = a[x][0] + a[x][1] + a[x][2], ty = a[y][0] + a[y][1] + a[y][2]; if (ok && Math.abs(tx - ty) <= 10) count++; }
        return count;
    }
}
```
