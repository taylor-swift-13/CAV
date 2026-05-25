# plus_one_digits

## Problem

Return the decimal digit string representing one more than nonnegative integer string `digits`.

## Requirements

- `digits` is a nonempty string of decimal digits.
- No leading zeros appear unless the whole value is exactly `0`.
- Return the full decimal representation after adding one.
- Carry propagation must work across one or more trailing `9` digits.

## Source

- Source: LeetCode problem `plus-one`.
- URL: https://leetcode.com/problems/plus-one/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class PlusOneDigits {
    public static String plus_one_digits(String digits) {
        char[] out = digits.toCharArray();
        int carry = 1;
        for (int i = out.length - 1; i >= 0 && carry != 0; i--) {
            int v = out[i] - '0' + carry;
            out[i] = (char)('0' + (v % 10));
            carry = v / 10;
        }
        return carry == 0 ? new String(out) : "1" + new String(out);
    }
}
```
