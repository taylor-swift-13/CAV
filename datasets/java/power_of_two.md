# power_of_two

## Problem

Return true if `n` is an exact positive power of two.

## Requirements

- `n` is a signed 32-bit integer.
- Only positive values can be powers of two.
- `1` is a power of two because it equals `2^0`.
- Return false for zero, negatives, odd numbers greater than one, and numbers with any odd factor.

## Source

- Source: LeetCode problem `power-of-two`.
- URL: https://leetcode.com/problems/power-of-two/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class PowerOfTwo {
    public static boolean power_of_two(int n) {
        if (n <= 0) return false;
        while (n % 2 == 0) n /= 2;
        return n == 1;
    }
}
```
