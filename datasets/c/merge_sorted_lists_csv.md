# merge_sorted_lists_csv

## Problem

Treat `a` and `b` as sorted linked lists encoded by comma-separated integers and return their sorted merge.

## Requirements

- Each input is a sorted comma-separated integer list with no spaces.
- The empty string represents an empty list.
- Return all values in nondecreasing order.
- At most 64 integers are encoded per input.

## Source

- Source: LeetCode problem `merge-two-sorted-lists`.
- URL: https://leetcode.com/problems/merge-two-sorted-lists/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
char *merge_sorted_lists_csv(const char *a, const char *b) {
    int av[64], bv[64];
    int an = 0, bn = 0, i = 0;
    while (a[i] != '\0') { int sign = 1; if (a[i] == '-') { sign = -1; i++; } int v = 0; while (a[i] >= '0' && a[i] <= '9') { v = v * 10 + a[i] - '0'; i++; } av[an++] = sign * v; if (a[i] == ',') i++; }
    i = 0;
    while (b[i] != '\0') { int sign = 1; if (b[i] == '-') { sign = -1; i++; } int v = 0; while (b[i] >= '0' && b[i] <= '9') { v = v * 10 + b[i] - '0'; i++; } bv[bn++] = sign * v; if (b[i] == ',') i++; }
    char *out = (char *)malloc(512);
    int ai = 0, bi = 0, pos = 0, first = 1;
    while (ai < an || bi < bn) {
        int v;
        if (bi >= bn || (ai < an && av[ai] <= bv[bi])) v = av[ai++]; else v = bv[bi++];
        pos += sprintf(out + pos, "%s%d", first ? "" : ",", v);
        first = 0;
    }
    out[pos] = '\0';
    return out;
}
```
