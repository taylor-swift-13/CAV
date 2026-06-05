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

```c
#include <stdlib.h>
char *add_binary_strings(const char *a, const char *b) {
    int na = 0, nb = 0;
    while (a[na] != '\0') na++;
    while (b[nb] != '\0') nb++;
    char tmp[256];
    int pos = 0;
    int i = na - 1, j = nb - 1, carry = 0;
    while (i >= 0 || j >= 0 || carry) {
        int sum = carry;
        if (i >= 0) sum += a[i--] - '0';
        if (j >= 0) sum += b[j--] - '0';
        tmp[pos] = (char)('0' + (sum % 2)); pos++;
        carry = sum / 2;
    }
    char *out = (char *)malloc((unsigned long)pos + 1);
    for (int k = 0; k < pos; k++) out[k] = tmp[pos - 1 - k];
    out[pos] = '\0';
    return out;
}
```
