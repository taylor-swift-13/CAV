# LC String To Integer Atoi Value

## Problem

Parse a string as a 32-bit signed integer following atoi rules.

## Requirements

- Skip leading spaces, parse optional sign and digits, then clamp to 32-bit signed range.

## Source

- Source: LeetCode problem `string-to-integer-atoi`.
- URL: https://leetcode.com/problems/string-to-integer-atoi/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcAtoiValue {
    public static int lc_atoi_value(String s) {
        int i = 0, sign = 1; while (i < s.length() && s.charAt(i) == ' ') i++; if (i < s.length() && (s.charAt(i) == '+' || s.charAt(i) == '-')) { if (s.charAt(i) == '-') sign = -1; i++; } long val = 0; while (i < s.length() && Character.isDigit(s.charAt(i))) { val = val * 10 + s.charAt(i) - '0'; if (sign == 1 && val > Integer.MAX_VALUE) return Integer.MAX_VALUE; if (sign == -1 && val > 2147483648L) return Integer.MIN_VALUE; i++; } return (int)(sign * val);
    }
}
```
