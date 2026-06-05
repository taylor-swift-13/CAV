# reverse_list_csv

## Problem

Treat comma-separated integer string `list` as a linked list and return its values in reverse order.

## Requirements

- `list` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty list.
- Return a comma-separated string using the same integer spelling after parsing.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `reverse-linked-list`.
- URL: https://leetcode.com/problems/reverse-linked-list/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
#include <stdlib.h>
#include <stdio.h>
char *reverse_list_csv(const char *list) {
    int values[64];
    int n = 0;
    int i = 0;
    while (list[i] != '\0') {
        int sign = 1;
        if (list[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (list[i] >= '0' && list[i] <= '9') { v = v * 10 + (list[i] - '0'); i++; }
        values[n++] = sign * v;
        if (list[i] == ',') i++;
    }
    char *out = (char *)malloc(512);
    int pos = 0;
    for (int k = n - 1; k >= 0; k--) pos += sprintf(out + pos, "%s%d", k == n - 1 ? "" : ",", values[k]);
    out[pos] = '\0';
    return out;
}
```
