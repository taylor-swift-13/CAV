# LC Hand Of Straights Bool

## Problem

Return true if the hand can be rearranged into groups of consecutive cards.

## Requirements

- `hand` is a comma-separated list of card values.
- `group_size > 0`.

## Source

- Source: LeetCode problem `hand-of-straights`.
- URL: https://leetcode.com/problems/hand-of-straights/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_hand_of_straights_bool(const char *hand, int group_size) {
    int a[512], n = 0, i = 0; while (hand[i] != '\0') { int v = 0; while (hand[i] >= '0' && hand[i] <= '9') { v = v * 10 + hand[i] - '0'; i++; } a[n++] = v; if (hand[i] == ',') i++; } if (n % group_size != 0) return 0; for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; } int used[512] = {0}; for (int x = 0; x < n; x++) if (!used[x]) { int need = a[x]; for (int g = 0; g < group_size; g++) { int found = -1; for (int y = 0; y < n; y++) if (!used[y] && a[y] == need) { found = y; break; } if (found < 0) return 0; used[found] = 1; need++; } } return 1;
}
```
