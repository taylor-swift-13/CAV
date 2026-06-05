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

```c
static int lc4_parse(const char *s, int out[128]) { int n = 0, i = 0; while (s[i] != '\0') { int sign = 1, v = 0; if (s[i] == '-') { sign = -1; i++; } while (s[i] >= '0' && s[i] <= '9') { v = v * 10 + s[i] - '0'; i++; } out[n++] = sign * v; if (s[i] == ',') i++; } return n; }
int lc_four_sum_ii_count(const char *a, const char *b, const char *c, const char *d) {
    int aa[128], bb[128], cc[128], dd[128]; int na = lc4_parse(a, aa), nb = lc4_parse(b, bb), nc = lc4_parse(c, cc), nd = lc4_parse(d, dd); int ans = 0; for (int i = 0; i < na; i++) for (int j = 0; j < nb; j++) for (int k = 0; k < nc; k++) for (int l = 0; l < nd; l++) if (aa[i] + bb[j] + cc[k] + dd[l] == 0) ans++; return ans;
}
```
