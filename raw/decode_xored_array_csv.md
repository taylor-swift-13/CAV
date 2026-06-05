# decode_xored_array_csv

## Problem

Given comma-separated XOR-encoded values and the first original value, return the decoded array.

## Requirements

- `encoded[i] = arr[i] XOR arr[i+1]`.
- `encoded` is comma-separated nonnegative integers.
- The empty string means the original array only contains `first`.
- Return the decoded array as comma-separated integers.

## Source

- Source: LeetCode problem `decode-xored-array`.
- URL: https://leetcode.com/problems/decode-xored-array/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
#include <stdlib.h>
#include <stdio.h>
char *decode_xored_array_csv(const char *encoded, int first) {
    char *out = (char *)malloc(512);
    int pos = sprintf(out, "%d", first);
    int cur = first;
    int i = 0;
    while (encoded[i] != '\0') { int v = 0; while (encoded[i] >= '0' && encoded[i] <= '9') { v = v * 10 + (encoded[i] - '0'); i++; } cur = cur ^ v; pos += sprintf(out + pos, ",%d", cur); if (encoded[i] == ',') i++; }
    return out;
}
```
