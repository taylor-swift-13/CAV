# Luogu P5723 Prime Sum Count

## Problem

Return how many consecutive primes starting from `2` can be added without the sum exceeding `limit`.

## Requirements

- `limit >= 0`.
- Primes are considered in increasing order.

## Source

- Source: Luogu problem `P5723`.
- URL: https://www.luogu.com.cn/problem/P5723
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5723PrimeSumCount {
    public static int luogu_p5723_prime_sum_count(int limit) {
        int sum = 0, count = 0;
        for (int x = 2; x <= limit; x++) { boolean prime = true; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = false; if (prime) { if (sum + x > limit) break; sum += x; count++; } }
        return count;
    }
}
```
