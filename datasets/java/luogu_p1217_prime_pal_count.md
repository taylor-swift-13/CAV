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

```java
class LuoguP1217PrimePalCount {
    static boolean pal(int x) { int r = 0, y = x; while (y > 0) { r = r * 10 + y % 10; y /= 10; } return r == x; }
    static boolean prime(int x) { if (x < 2) return false; for (int d = 2; d * d <= x; d++) if (x % d == 0) return false; return true; }
    public static int luogu_p1217_prime_pal_count(int a, int b) { int count = 0; for (int x = a; x <= b; x++) if (pal(x) && prime(x)) count++; return count; }
}
```
