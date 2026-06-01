# LC Sort Colors Code CSV

## Problem

Sort comma-separated colors `0`, `1`, and `2`, then return the decimal code formed by the sorted colors.

## Requirements

- This scalar return is a deterministic encoding of the original sorted-array output.
- The supplied arrays have at most 9 elements.

## Source

- Source: LeetCode problem `sort-colors`.
- URL: https://leetcode.com/problems/sort-colors/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcSortColorsCodeCsv {
    public static int lc_sort_colors_code_csv(String colors) {
        int[] cnt = new int[3]; for (String p : colors.split(",")) cnt[Integer.parseInt(p)]++; int code = 0; for (int v = 0; v < 3; v++) for (int k = 0; k < cnt[v]; k++) code = code * 10 + v; return code;
    }
}
```
