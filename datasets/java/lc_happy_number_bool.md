# LC Happy Number Bool

## Problem

Return true if repeated sum-of-squares of digits reaches `1`.

## Requirements

- `n > 0`.
- Use cycle detection by the known bounded digit-square process.

## Source

- Source: LeetCode problem `happy-number`.
- URL: https://leetcode.com/problems/happy-number/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcHappyNumberBool {
    public static boolean lc_happy_number_bool(int n) {
        boolean[] seen = new boolean[1000]; while (n != 1 && !seen[n]) { seen[n] = true; int s = 0; while (n > 0) { int d = n % 10; s += d * d; n /= 10; } n = s; } return n == 1;
    }
}
```
