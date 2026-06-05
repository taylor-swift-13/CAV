# LC Keys And Rooms Bool

## Problem

Return true if every room can be visited starting from room `0`.

## Requirements

- Rooms are semicolon-separated.
- Keys inside a room are comma-separated room numbers; `-` encodes no keys.

## Source

- Source: LeetCode problem `keys-and-rooms`.
- URL: https://leetcode.com/problems/keys-and-rooms/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_keys_and_rooms_bool(const char *rooms) {
    int keys[128][128], deg[128] = {0}, n = 0, i = 0; while (rooms[i] != '\0') { if (rooms[i] == '-') i++; else while (rooms[i] != '\0' && rooms[i] != ';') { int v = 0; while (rooms[i] >= '0' && rooms[i] <= '9') { v = v * 10 + (rooms[i] - '0'); i++; } keys[n][deg[n]++] = v; if (rooms[i] == ',') i++; } n++; if (rooms[i] == ';') i++; }
    int seen[128] = {0}, stack[128], top = 0, count = 0; stack[top] = 0; top++; seen[0] = 1; while (top > 0) { int v = stack[--top]; count++; for (int k = 0; k < deg[v]; k++) if (!seen[keys[v][k]]) { seen[keys[v][k]] = 1; stack[top] = keys[v][k]; top++; } } return count == n;
}
```
