# Luogu P5724 Range CSV

## Problem

Return the difference between the maximum and minimum value in a comma-separated integer list.

## Requirements

- `nums` is nonempty.
- Values fit in signed 32-bit integer range.

## Source

- Source: Luogu problem `P5724`.
- URL: https://www.luogu.com.cn/problem/P5724
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5724RangeCsv {
    public static int luogu_p5724_range_csv(String nums) {
        String[] p = nums.split(","); int mn = Integer.parseInt(p[0]), mx = mn; for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < mn) mn = v; if (v > mx) mx = v; } return mx - mn;
    }
}
```
