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

```c
char *plus_one_digits(const char *digits) {
    int n = 0;
    while (digits[n] != '\0') n++;
    char *out = (char *)malloc((unsigned long)n + 2);
    for (int i = 0; i < n; i++) out[i + 1] = digits[i];
    out[n + 1] = '\0';
    int i = n;
    int carry = 1;
    while (i >= 1 && carry) {
        int v = out[i] - '0' + carry;
        out[i] = (char)('0' + (v % 10));
        carry = v / 10;
        i--;
    }
    if (carry) { out[0] = '1'; return out; }
    for (int j = 0; j <= n; j++) out[j] = out[j + 1];
    return out;
}
```
