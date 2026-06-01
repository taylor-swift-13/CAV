# LC Largest Component By Common Factor CSV

## Problem

Return the size of the largest component where two numbers are connected if they share a factor greater than 1.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `largest-component-size-by-common-factor`.
- URL: https://leetcode.com/problems/largest-component-size-by-common-factor/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLargestComponentCommonFactorCsv {
    static int gcd(int a, int b) { while (b != 0) { int t = a % b; a = b; b = t; } return a; }
    public static int lc_largest_component_common_factor_csv(String nums) {
        String[] p = nums.split(","); int n = p.length; int[] a = new int[n]; for (int i = 0; i < n; i++) a[i] = Integer.parseInt(p[i]); boolean[][] g = new boolean[n][n]; for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (gcd(a[i], a[j]) > 1) { g[i][j] = true; g[j][i] = true; } boolean[] seen = new boolean[n]; int best = 0; int[] q = new int[n]; for (int s = 0; s < n; s++) if (!seen[s]) { int head = 0, tail = 0, cnt = 0; q[tail++] = s; seen[s] = true; while (head < tail) { int v = q[head++]; cnt++; for (int to = 0; to < n; to++) if (g[v][to] && !seen[to]) { seen[to] = true; q[tail++] = to; } } best = Math.max(best, cnt); } return best;
    }
}
```
