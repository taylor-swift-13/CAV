# Luogu P5718 Minimum CSV

## Problem

Return the minimum value in a comma-separated integer list.

## Requirements

- `nums` is nonempty.
- Values fit in signed 32-bit integer range.

## Source

- Source: Luogu problem `P5718`.
- URL: https://www.luogu.com.cn/problem/P5718
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5718MinCsv {
    public static int luogu_p5718_min_csv(String nums) {
        String[] p = nums.split(","); int best = Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < best) best = v; } return best;
    }
}
```
