# LC Minimum Genetic Mutation Steps

## Problem

Return the minimum number of single-character mutations from `start` to `end`.

## Requirements

- Each intermediate gene must appear in comma-separated `bank`.
- Genes have length 8 and use `A`, `C`, `G`, `T`.

## Source

- Source: LeetCode problem `minimum-genetic-mutation`.
- URL: https://leetcode.com/problems/minimum-genetic-mutation/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
static int lc_mgm_diff1(const char *a, const char *b) { int d = 0; for (int i = 0; i < 8; i++) if (a[i] != b[i]) d++; return d == 1; }
int lc_min_genetic_mutation_steps(const char *start, const char *end, const char *bank) {
    char genes[128][9]; int n = 0, i = 0, col = 0; while (bank[i] != '\0') { col = 0; while (bank[i] != ',' && bank[i] != '\0') genes[n][col++] = bank[i++]; genes[n][col] = '\0'; n++; if (bank[i] == ',') i++; }
    int q[128], dist[128], seen[128] = {0}, h = 0, t = 0; for (int k = 0; k < n; k++) if (lc_mgm_diff1(start, genes[k])) { q[t] = k; dist[t++] = 1; seen[k] = 1; } while (h < t) { int v = q[h], d = dist[h++]; int same = 1; for (int k = 0; k < 8; k++) if (genes[v][k] != end[k]) same = 0; if (same) return d; for (int to = 0; to < n; to++) if (!seen[to] && lc_mgm_diff1(genes[v], genes[to])) { seen[to] = 1; q[t] = to; dist[t++] = d + 1; } } return -1;
}
```
