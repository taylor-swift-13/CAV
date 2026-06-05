# Luogu P2678 Jump Stone Distance

## Problem

Return the largest possible minimum jump distance after removing at most `remove` stones.

## Requirements

- `length` is the river length.
- `stones` is a comma-separated sorted list of internal stone positions.

## Source

- Source: Luogu problem `P2678`.
- URL: https://www.luogu.com.cn/problem/P2678
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p2678_jump_stone_distance(int length, const char *stones, int remove) {
    int a[512], n = 0, i = 0; while (stones[i] != '\0') { int v = 0; while (stones[i] >= '0' && stones[i] <= '9') { v = v * 10 + (stones[i] - '0'); i++; } a[n++] = v; if (stones[i] == ',') i++; } a[n++] = length; int lo = 1, hi = length, ans = 0; while (lo <= hi) { int mid = lo + (hi - lo) / 2, last = 0, removed = 0; for (int x = 0; x < n; x++) { if (a[x] - last < mid) removed++; else last = a[x]; } if (removed <= remove) { ans = mid; lo = mid + 1; } else hi = mid - 1; } return ans;
}
```
