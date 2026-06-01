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

```java
class LcGasStationStartCsv {
    public static int lc_gas_station_start_csv(String gas, String cost) {
        String[] gp = gas.split(","), cp = cost.split(","); int total = 0, tank = 0, start = 0; for (int i = 0; i < gp.length; i++) { int d = Integer.parseInt(gp[i]) - Integer.parseInt(cp[i]); total += d; tank += d; if (tank < 0) { start = i + 1; tank = 0; } } return total >= 0 ? start : -1;
    }
}
```
