# Luogu P5740 Best Total Score

## Problem

Return the maximum total score among students encoded as triples `chinese,math,english;...`.

## Requirements

- The empty string returns `0`.
- Scores are nonnegative integers.

## Source

- Source: Luogu problem `P5740`.
- URL: https://www.luogu.com.cn/problem/P5740
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5740_best_total_score(const char *rows) {
    int best = 0, i = 0;
    while (rows[i] != '\0') { int total = 0; for (int k = 0; k < 3; k++) { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } total += v; if (rows[i] == ',') i++; } if (total > best) best = total; if (rows[i] == ';') i++; }
    return best;
}
```
