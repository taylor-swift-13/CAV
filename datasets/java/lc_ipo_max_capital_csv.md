# LC IPO Max Capital CSV

## Problem

Return maximized capital after selecting at most `k` projects.

## Requirements

- `profits` and `capital` are comma-separated arrays of equal length.
- Each project can be selected at most once.

## Source

- Source: LeetCode problem `ipo`.
- URL: https://leetcode.com/problems/ipo/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcIpoMaxCapitalCsv {
    public static int lc_ipo_max_capital_csv(int k, int w, String profits, String capital) {
        String[] pp = profits.split(","), cc = capital.split(","); int n = pp.length; int[] p = new int[n], c = new int[n]; for (int i = 0; i < n; i++) { p[i] = Integer.parseInt(pp[i]); c[i] = Integer.parseInt(cc[i]); } boolean[] used = new boolean[n]; for (int step = 0; step < k; step++) { int best = -1; for (int i = 0; i < n; i++) if (!used[i] && c[i] <= w && (best < 0 || p[i] > p[best])) best = i; if (best < 0) break; used[best] = true; w += p[best]; } return w;
    }
}
```
