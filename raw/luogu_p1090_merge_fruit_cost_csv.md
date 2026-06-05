# Luogu P1090 Merge Fruit Cost CSV

## Problem

Return the minimum total cost of repeatedly merging the two smallest piles.

## Requirements

- `piles` is a nonempty comma-separated list of positive integers.
- This is the Huffman-style greedy objective from Luogu P1090.

## Source

- Source: Luogu problem `P1090`.
- URL: https://www.luogu.com.cn/problem/P1090
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p1090_merge_fruit_cost_csv(const char *piles) {
    int a[512], n = 0, i = 0; while (piles[i] != '\0') { int v = 0; while (piles[i] >= '0' && piles[i] <= '9') { v = v * 10 + (piles[i] - '0'); i++; } a[n++] = v; if (piles[i] == ',') i++; }
    int cost = 0; while (n > 1) { for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; } int merged = a[0] + a[1]; cost += merged; a[1] = merged; for (int x = 2; x < n; x++) a[x - 1] = a[x]; n--; } return cost;
}
```
