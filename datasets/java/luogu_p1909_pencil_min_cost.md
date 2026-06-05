# Luogu P1909 Pencil Min Cost

## Problem

Return the minimum cost to buy at least `n` pencils.

## Requirements

- `options` is semicolon-separated `pack_size,price` records.
- Each purchase uses only one supplier option.

## Source

- Source: Luogu problem `P1909`.
- URL: https://www.luogu.com.cn/problem/P1909
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP1909PencilMinCost {
    public static int luogu_p1909_pencil_min_cost(int n, String options) {
        int best = Integer.MAX_VALUE; for (String rec : options.split(";")) { String[] p = rec.split(","); int pack = Integer.parseInt(p[0]), price = Integer.parseInt(p[1]); best = Math.min(best, ((n + pack - 1) / pack) * price); } return best;
    }
}
```
