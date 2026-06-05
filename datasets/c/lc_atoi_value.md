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

```c
int lc_atoi_value(const char *s) {
    int i = 0, sign = 1; while (s[i] == ' ') i++; if (s[i] == '+' || s[i] == '-') { if (s[i] == '-') sign = -1; i++; } long long val = 0; while (s[i] >= '0' && s[i] <= '9') { val = val * 10 + s[i] - '0'; if (sign == 1 && val > 2147483647LL) return 2147483647; if (sign == -1 && val > 2147483648LL) return -2147483647 - 1; i++; } return (int)(sign * val);
}
```
