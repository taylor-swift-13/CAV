# Luogu P1003 Carpet Top Index

## Problem

Return the topmost carpet covering a query point, or `-1` if none covers it.

## Requirements

- `carpets` is semicolon-separated `x,y,width,height` records.
- Return the 1-based carpet index matching Luogu P1003 order.

## Source

- Source: Luogu problem `P1003`.
- URL: https://www.luogu.com.cn/problem/P1003
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p1003_carpet_top_index(const char *carpets, int x, int y) {
    int ans = -1, idx = 1, i = 0; while (carpets[i] != '\0') { int v[4] = {0,0,0,0}; for (int k = 0; k < 4; k++) { while (carpets[i] >= '0' && carpets[i] <= '9') { v[k] = v[k] * 10 + carpets[i] - '0'; i++; } if (carpets[i] == ',') i++; } if (x >= v[0] && x <= v[0] + v[2] && y >= v[1] && y <= v[1] + v[3]) ans = idx; idx++; if (carpets[i] == ';') i++; } return ans;
}
```
