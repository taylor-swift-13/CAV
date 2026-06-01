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

```java
class LcCountPrimesBelow {
    public static int lc_count_primes_below(int n) {
        if (n <= 2) return 0; boolean[] is = new boolean[n]; for (int i = 2; i < n; i++) is[i] = true; for (int p = 2; p * p < n; p++) if (is[p]) for (int x = p * p; x < n; x += p) is[x] = false; int ans = 0; for (int i = 2; i < n; i++) if (is[i]) ans++; return ans;
    }
}
```
