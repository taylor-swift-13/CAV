# LC 4Sum II Count

## Problem

Return the number of tuples `i,j,k,l` with `a[i]+b[j]+c[k]+d[l] == 0`.

## Requirements

- Arrays are comma-separated signed integer lists.

## Source

- Source: LeetCode problem `4sum-ii`.
- URL: https://leetcode.com/problems/4sum-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcFourSumIiCount {
    static int[] parse(String s) { String[] p = s.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); return a; }
    public static int lc_four_sum_ii_count(String a, String b, String c, String d) {
        int[] aa = parse(a), bb = parse(b), cc = parse(c), dd = parse(d); int ans = 0; for (int x : aa) for (int y : bb) for (int z : cc) for (int w : dd) if (x + y + z + w == 0) ans++; return ans;
    }
}
```
