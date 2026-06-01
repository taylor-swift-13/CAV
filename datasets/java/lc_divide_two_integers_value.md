# LC Divide Two Integers Value

## Problem

Return integer quotient truncated toward zero with 32-bit overflow clamp.

## Requirements

- This preserves the original divide-two-integers result contract.

## Source

- Source: LeetCode problem `divide-two-integers`.
- URL: https://leetcode.com/problems/divide-two-integers/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcDivideTwoIntegersValue {
    public static int lc_divide_two_integers_value(int dividend, int divisor) {
        if (dividend == Integer.MIN_VALUE && divisor == -1) return Integer.MAX_VALUE; return dividend / divisor;
    }
}
```
