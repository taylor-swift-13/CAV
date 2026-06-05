# middle_node_value_csv

## Problem

Treat comma-separated integer string `list` as a linked list and return the value of its middle node.

## Requirements

- `list` is nonempty and comma-separated with no spaces.
- For an even number of nodes, return the second middle value.
- Return the node value, not the index.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `middle-of-the-linked-list`.
- URL: https://leetcode.com/problems/middle-of-the-linked-list/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int middle_node_value_csv(const char *list) {
    int values[64];
    int n = 0;
    int i = 0;
    while (list[i] != '\0') {
        int sign = 1;
        if (list[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (list[i] >= '0' && list[i] <= '9') { v = v * 10 + list[i] - '0'; i++; }
        values[n++] = sign * v;
        if (list[i] == ',') i++;
    }
    return values[n / 2];
}
```
