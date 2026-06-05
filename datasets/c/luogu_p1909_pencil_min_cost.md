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

```c
int luogu_p1909_pencil_min_cost(int n, const char *options) {
    int best = 2147483647, i = 0; while (options[i] != '\0') { int pack = 0, price = 0; while (options[i] >= '0' && options[i] <= '9') { pack = pack * 10 + options[i] - '0'; i++; } if (options[i] == ',') i++; while (options[i] >= '0' && options[i] <= '9') { price = price * 10 + options[i] - '0'; i++; } int cost = ((n + pack - 1) / pack) * price; if (cost < best) best = cost; if (options[i] == ';') i++; } return best;
}
```
