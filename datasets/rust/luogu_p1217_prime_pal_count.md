# Luogu P1217 Prime Palindrome Count

## Problem

Return how many palindromic primes lie in `[a,b]`.

## Requirements

- This follows the prime-palindrome search task from Luogu P1217.
- `a <= b`.

## Source

- Source: Luogu problem `P1217`.
- URL: https://www.luogu.com.cn/problem/P1217
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p1217_prime_pal_count(a: i32, b: i32) -> i32 {
    fn pal(x: i32) -> bool { let mut r = 0; let mut y = x; while y > 0 { r = r * 10 + y % 10; y /= 10; } r == x }
    fn prime(x: i32) -> bool { if x < 2 { return false; } let mut d = 2; while d * d <= x { if x % d == 0 { return false; } d += 1; } true }
    let mut count = 0; let mut x = a; while x <= b { if pal(x) && prime(x) { count += 1; } x += 1; } count
}
```
