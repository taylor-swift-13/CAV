# LC Shortest Unsorted Continuous Subarray Length CSV

## Problem

Return the shortest subarray length that must be sorted to make the whole array sorted.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `shortest-unsorted-continuous-subarray`.
- URL: https://leetcode.com/problems/shortest-unsorted-continuous-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcShortestUnsortedLenCsv {
    public static int lc_shortest_unsorted_len_csv(String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length], b = new int[p.length]; for (int i = 0; i < p.length; i++) { a[i] = Integer.parseInt(p[i]); b[i] = a[i]; } java.util.Arrays.sort(b); int l = 0; while (l < a.length && a[l] == b[l]) l++; if (l == a.length) return 0; int r = a.length - 1; while (r >= 0 && a[r] == b[r]) r--; return r - l + 1;
    }
}
```
