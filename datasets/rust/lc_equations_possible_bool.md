# LC Equality Equations Possible Bool

## Problem

Return true if all equality and inequality equations can be satisfied.

## Requirements

- Equations are separated by semicolons, e.g. `a==b;b!=c`.
- Variables are lowercase English letters.

## Source

- Source: LeetCode problem `satisfiability-of-equality-equations`.
- URL: https://leetcode.com/problems/satisfiability-of-equality-equations/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_equations_possible_bool(equations: &str) -> bool {
    fn find(p: &mut Vec<usize>, x: usize) -> usize { if p[x] != x { let r = find(p, p[x]); p[x] = r; } p[x] } let mut p: Vec<usize> = (0..26).collect(); for e in equations.split(';') { let b = e.as_bytes(); if b[1] == b'=' { let a = find(&mut p, (b[0] - b'a') as usize); let c = find(&mut p, (b[3] - b'a') as usize); p[a] = c; } } for e in equations.split(';') { let b = e.as_bytes(); if b[1] == b'!' { let a = find(&mut p, (b[0] - b'a') as usize); let c = find(&mut p, (b[3] - b'a') as usize); if a == c { return false; } } } true
}
```
