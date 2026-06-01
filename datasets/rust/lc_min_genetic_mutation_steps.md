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

```rust
pub fn lc_min_genetic_mutation_steps(start: &str, end: &str, bank: &str) -> i32 {
    fn diff1(a: &str, b: &str) -> bool { a.bytes().zip(b.bytes()).filter(|(x, y)| x != y).count() == 1 }
    let genes: Vec<&str> = bank.split(',').collect(); let mut q: Vec<(usize, i32)> = Vec::new(); let mut seen = vec![false; genes.len()]; for i in 0..genes.len() { if diff1(start, genes[i]) { q.push((i, 1)); seen[i] = true; } } let mut h = 0usize; while h < q.len() { let (v, d) = q[h]; h += 1; if genes[v] == end { return d; } for to in 0..genes.len() { if !seen[to] && diff1(genes[v], genes[to]) { seen[to] = true; q.push((to, d + 1)); } } } -1
}
```
