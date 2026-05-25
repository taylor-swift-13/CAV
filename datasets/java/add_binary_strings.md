# add_binary_strings

## Problem

Return the binary sum of nonempty binary strings `a` and `b`.

## Requirements

- Inputs contain only `0` and `1`.
- Inputs are nonempty.
- Do digit-by-digit binary addition; do not require conversion to machine integer width.
- Return no leading zeros except the single string `0`.

## Source

- Source: LeetCode problem `add-binary`.
- URL: https://leetcode.com/problems/add-binary/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class AddBinaryStrings {
    public static String add_binary_strings(String a, String b) {
        StringBuilder out = new StringBuilder();
        int i = a.length() - 1, j = b.length() - 1, carry = 0;
        while (i >= 0 || j >= 0 || carry != 0) {
            int sum = carry;
            if (i >= 0) sum += a.charAt(i--) - '0';
            if (j >= 0) sum += b.charAt(j--) - '0';
            out.append((char)('0' + (sum % 2)));
            carry = sum / 2;
        }
        return out.reverse().toString();
    }
}
```
