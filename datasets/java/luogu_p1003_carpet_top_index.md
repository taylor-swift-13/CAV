# Luogu P1003 Carpet Top Index

## Problem

Return the topmost carpet covering a query point, or `-1` if none covers it.

## Requirements

- `carpets` is semicolon-separated `x,y,width,height` records.
- Return the 1-based carpet index matching Luogu P1003 order.

## Source

- Source: Luogu problem `P1003`.
- URL: https://www.luogu.com.cn/problem/P1003
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP1003CarpetTopIndex {
    public static int luogu_p1003_carpet_top_index(String carpets, int x, int y) {
        int ans = -1, idx = 1; for (String rec : carpets.split(";")) { String[] p = rec.split(","); int a = Integer.parseInt(p[0]), b = Integer.parseInt(p[1]), g = Integer.parseInt(p[2]), k = Integer.parseInt(p[3]); if (x >= a && x <= a + g && y >= b && y <= b + k) ans = idx; idx++; } return ans;
    }
}
```
