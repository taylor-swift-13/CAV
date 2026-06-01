# LC Count Primes Below

## Problem

Return the number of prime numbers strictly less than `n`.

## Requirements

- `0 <= n <= 10000`.

## Source

- Source: LeetCode problem `count-primes`.
- URL: https://leetcode.com/problems/count-primes/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_count_primes_below(n: i32) -> i32 {
    if n <= 2 { return 0; } let nn = n as usize; let mut is = vec![true; nn]; is[0] = false; is[1] = false; let mut p = 2usize; while p * p < nn { if is[p] { let mut x = p * p; while x < nn { is[x] = false; x += p; } } p += 1; } let mut ans = 0; for v in is { if v { ans += 1; } } ans
}
```
