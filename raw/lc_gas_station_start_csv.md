# LC Gas Station Start CSV

## Problem

Return the starting gas station index that completes the circuit, or `-1`.

## Requirements

- `gas` and `cost` are comma-separated arrays of equal positive length.
- The original problem guarantees uniqueness when a solution exists.

## Source

- Source: LeetCode problem `gas-station`.
- URL: https://leetcode.com/problems/gas-station/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_gas_station_start_csv(const char *gas, const char *cost) {
    int g[256], c[256], n = 0, i = 0; while (gas[i] != '\0') { int v = 0; while (gas[i] >= '0' && gas[i] <= '9') { v = v * 10 + (gas[i] - '0'); i++; } g[n] = v; n++; if (gas[i] == ',') i++; } i = 0; int m = 0; while (cost[i] != '\0') { int v = 0; while (cost[i] >= '0' && cost[i] <= '9') { v = v * 10 + (cost[i] - '0'); i++; } c[m] = v; m++; if (cost[i] == ',') i++; }
    int total = 0, tank = 0, start = 0; for (int k = 0; k < n; k++) { int d = g[k] - c[k]; total += d; tank += d; if (tank < 0) { start = k + 1; tank = 0; } } return total >= 0 ? start : -1;
}
```
