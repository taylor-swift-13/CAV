# LC Kth Largest Element CSV

## Problem

Return the `k`th largest value in comma-separated `nums`.

## Requirements

- `nums` is nonempty.
- `1 <= k <= len(nums)`.

## Source

- Source: LeetCode problem `kth-largest-element-in-an-array`.
- URL: https://leetcode.com/problems/kth-largest-element-in-an-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcKthLargestCsv {
    public static int lc_kth_largest_csv(String nums, int k) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); return a[a.length - k];
    }
}
```
