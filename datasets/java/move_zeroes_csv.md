# move_zeroes_csv

## Problem

Move all zeroes in comma-separated integer array `nums` to the end while preserving nonzero order.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Preserve relative order of nonzero values.
- Return the transformed array encoding.

## Source

- Source: LeetCode problem `move-zeroes`.
- URL: https://leetcode.com/problems/move-zeroes/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class MoveZeroesCsv {
    public static String move_zeroes_csv(String nums) {
        if (nums.isEmpty()) return "";
        String[] parts = nums.split(",");
        StringBuilder out = new StringBuilder();
        int zeros = 0;
        for (String p : parts) { int v = Integer.parseInt(p); if (v == 0) zeros++; else { if (out.length() > 0) out.append(','); out.append(v); } }
        for (int i = 0; i < zeros; i++) { if (out.length() > 0) out.append(','); out.append(0); }
        return out.toString();
    }
}
```
