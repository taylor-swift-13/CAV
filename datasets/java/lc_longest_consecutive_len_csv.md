# LC Longest Consecutive Sequence Length CSV

## Problem

Return the length of the longest consecutive integer run in a comma-separated list.

## Requirements

- The empty string returns `0`.
- Duplicate values do not extend a run.

## Source

- Source: LeetCode problem `longest-consecutive-sequence`.
- URL: https://leetcode.com/problems/longest-consecutive-sequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLongestConsecutiveLenCsv {
    public static int lc_longest_consecutive_len_csv(String nums) {
        if (nums.isEmpty()) return 0; String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a);
        int best = 1, cur = 1; for (int i = 1; i < a.length; i++) { if (a[i] == a[i - 1]) continue; if (a[i] == a[i - 1] + 1) cur++; else cur = 1; if (cur > best) best = cur; }
        return best;
    }
}
```
