# LC H Index CSV

## Problem

Return the H-index for comma-separated citation counts.

## Requirements

- `citations` is a nonempty comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `h-index`.
- URL: https://leetcode.com/problems/h-index/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcHIndexCsv {
    public static int lc_h_index_csv(String citations) {
        String[] p = citations.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); int h = 0; for (int i = 0; i < a.length; i++) { int cand = a.length - i; if (a[i] >= cand && cand > h) h = cand; } return h;
    }
}
```
