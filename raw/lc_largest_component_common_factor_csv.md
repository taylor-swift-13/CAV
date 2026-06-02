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

```c
static int lc_gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
int lc_largest_component_common_factor_csv(const char *nums) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; } int g[256][256] = {{0}}; for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (lc_gcd_i(a[x], a[y]) > 1) { g[x][y] = 1; g[y][x] = 1; } int seen[256] = {0}, best = 0, q[256]; for (int s = 0; s < n; s++) if (!seen[s]) { int head = 0, tail = 0, cnt = 0; q[tail++] = s; seen[s] = 1; while (head < tail) { int v = q[head++]; cnt++; for (int to = 0; to < n; to++) if (g[v][to] && !seen[to]) { seen[to] = 1; q[tail++] = to; } } if (cnt > best) best = cnt; } return best;
}
```
