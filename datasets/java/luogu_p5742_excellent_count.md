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

```java
class LuoguP5742ExcellentCount {
    public static int luogu_p5742_excellent_count(String rows) {
        int ans = 0; for (String row : rows.split(";")) { String[] p = row.split(","); int a = Integer.parseInt(p[1]), q = Integer.parseInt(p[2]); if (a + q > 140 && 7 * a + 3 * q >= 800) ans++; } return ans;
    }
}
```
