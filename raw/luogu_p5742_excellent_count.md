# Luogu P5742 Excellent Count

## Problem

Count students satisfying Luogu P5742's excellent condition.

## Requirements

- Rows are encoded as `id,academic,quality;...`.
- A student is excellent if `academic + quality > 140` and `7*academic + 3*quality >= 800`.

## Source

- Source: Luogu problem `P5742`.
- URL: https://www.luogu.com.cn/problem/P5742
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5742_excellent_count(const char *rows) {
    int ans = 0, i = 0;
    while (rows[i] != '\0') { int id = 0, a = 0, q = 0; while (rows[i] >= '0' && rows[i] <= '9') { id = id * 10 + (rows[i] - '0'); i++; } if (rows[i] == ',') i++; while (rows[i] >= '0' && rows[i] <= '9') { a = a * 10 + (rows[i] - '0'); i++; } if (rows[i] == ',') i++; while (rows[i] >= '0' && rows[i] <= '9') { q = q * 10 + (rows[i] - '0'); i++; } if (a + q > 140 && 7 * a + 3 * q >= 800) ans++; if (rows[i] == ';') i++; }
    return ans;
}
```
