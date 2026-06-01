# LC Monotonic Array Bool CSV

## Problem

Return true if comma-separated `nums` is monotone nondecreasing or nonincreasing.

## Requirements

- `nums` is nonempty.

## Source

- Source: LeetCode problem `monotonic-array`.
- URL: https://leetcode.com/problems/monotonic-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMonotonicArrayBoolCsv {
    public static boolean lc_monotonic_array_bool_csv(String nums) {
        String[] p = nums.split(","); boolean inc = true, dec = true; int prev = Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < prev) inc = false; if (v > prev) dec = false; prev = v; } return inc || dec;
    }
}
```
