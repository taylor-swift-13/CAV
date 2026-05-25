# palindrome_number

## Problem

Return true if decimal representation of integer `x` reads the same forward and backward.

## Requirements

- `x` is a signed 32-bit integer.
- Negative numbers are not palindromes because the minus sign is not mirrored at the end.
- Single-digit nonnegative numbers, including zero, are palindromes.
- Numbers ending in zero are palindromes only when the number itself is zero.
- Return only a boolean result; do not convert invalid inputs or print explanations.

## Source

- Source: LeetCode problem `palindrome-number`.
- URL: https://leetcode.com/problems/palindrome-number/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class PalindromeNumber {
    public static boolean palindrome_number(int x) {
        if (x < 0) return false;
        int original = x;
        int rev = 0;
        while (x > 0) {
            rev = rev * 10 + x % 10;
            x /= 10;
        }
        return rev == original;
    }
}
```
