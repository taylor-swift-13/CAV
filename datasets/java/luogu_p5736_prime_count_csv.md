# Luogu P5736 Prime Count CSV

## Problem

Return how many comma-separated integers are prime.

## Requirements

- The empty string represents an empty list.
- Values are nonnegative.

## Source

- Source: Luogu problem `P5736`.
- URL: https://www.luogu.com.cn/problem/P5736
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5736PrimeCountCsv {
    public static int luogu_p5736_prime_count_csv(String nums) {
        if (nums.isEmpty()) return 0;
        int count = 0;
        for (String part : nums.split(",")) { int x = Integer.parseInt(part); boolean prime = x >= 2; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = false; if (prime) count++; }
        return count;
    }
}
```
