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

```java
class LcMinGeneticMutationSteps {
    static boolean diff1(String a, String b) { int d = 0; for (int i = 0; i < 8; i++) if (a.charAt(i) != b.charAt(i)) d++; return d == 1; }
    public static int lc_min_genetic_mutation_steps(String start, String end, String bank) {
        String[] genes = bank.split(","); int[] q = new int[genes.length], dist = new int[genes.length]; boolean[] seen = new boolean[genes.length]; int h = 0, t = 0; for (int i = 0; i < genes.length; i++) if (diff1(start, genes[i])) { q[t] = i; dist[t++] = 1; seen[i] = true; } while (h < t) { int v = q[h], d = dist[h++]; if (genes[v].equals(end)) return d; for (int to = 0; to < genes.length; to++) if (!seen[to] && diff1(genes[v], genes[to])) { seen[to] = true; q[t] = to; dist[t++] = d + 1; } } return -1;
    }
}
```
