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

```java
class LuoguP5740BestTotalScore {
    public static int luogu_p5740_best_total_score(String rows) {
        if (rows.isEmpty()) return 0;
        int best = 0;
        for (String row : rows.split(";")) { String[] p = row.split(","); int total = Integer.parseInt(p[0]) + Integer.parseInt(p[1]) + Integer.parseInt(p[2]); if (total > best) best = total; }
        return best;
    }
}
```
