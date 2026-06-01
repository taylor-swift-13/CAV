# LC Split Array Largest Sum CSV

## Problem

Split `nums` into `m` nonempty contiguous parts and minimize the largest part sum.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `split-array-largest-sum`.
- URL: https://leetcode.com/problems/split-array-largest-sum/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcSplitArrayLargestSumCsv {
    public static int lc_split_array_largest_sum_csv(String nums, int m) {
        String[] p = nums.split(","); int[] a = new int[p.length]; int lo = 0, hi = 0; for (int i = 0; i < p.length; i++) { a[i] = Integer.parseInt(p[i]); lo = Math.max(lo, a[i]); hi += a[i]; } while (lo < hi) { int mid = lo + (hi - lo) / 2, parts = 1, sum = 0; for (int v : a) { if (sum + v > mid) { parts++; sum = 0; } sum += v; } if (parts <= m) hi = mid; else lo = mid + 1; } return lo;
    }
}
```
