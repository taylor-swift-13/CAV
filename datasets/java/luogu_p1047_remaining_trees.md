# Luogu P1047 Remaining Trees

## Problem

Return how many integer tree positions remain after removing all interval-covered positions.

## Requirements

- The road has tree positions from `0` through `length`, inclusive.
- `intervals` is semicolon-separated `left,right` records with inclusive endpoints.

## Source

- Source: Luogu problem `P1047`.
- URL: https://www.luogu.com.cn/problem/P1047
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP1047RemainingTrees {
    public static int luogu_p1047_remaining_trees(int length, String intervals) {
        boolean[] removed = new boolean[length + 1]; for (String rec : intervals.split(";")) { String[] p = rec.split(","); int l = Integer.parseInt(p[0]), r = Integer.parseInt(p[1]); for (int x = l; x <= r && x <= length; x++) removed[x] = true; } int ans = 0; for (int x = 0; x <= length; x++) if (!removed[x]) ans++; return ans;
    }
}
```
