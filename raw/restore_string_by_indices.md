# restore_string_by_indices

## Problem

Restore a string by placing `s[i]` at index `indices[i]`; indices are comma-separated integers.

## Requirements

- `indices` is a permutation of `0..len(s)-1`.
- `indices` is comma-separated with no spaces.
- Return a string `out` such that `out[indices[i]] == s[i]`.
- Input strings are ASCII.

## Source

- Source: LeetCode problem `shuffle-string`.
- URL: https://leetcode.com/problems/shuffle-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
#include <stdlib.h>
char *restore_string_by_indices(const char *s, const char *indices) {
    int n = 0;
    while (s[n] != '\0') n++;
    char *out = (char *)malloc((unsigned long)n + 1);
    int pos = 0;
    int i = 0;
    while (indices[i] != '\0') {
        int v = 0;
        while (indices[i] >= '0' && indices[i] <= '9') { v = v * 10 + indices[i] - '0'; i++; }
        out[v] = s[pos++];
        if (indices[i] == ',') i++;
    }
    out[n] = '\0';
    return out;
}
```
