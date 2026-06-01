# LC Count Nice Pairs CSV

## Problem

Return the number of nice pairs where `nums[i] + rev(nums[j]) == nums[j] + rev(nums[i])`.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `count-nice-pairs-in-an-array`.
- URL: https://leetcode.com/problems/count-nice-pairs-in-an-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcCountNicePairsCsv {
    static int rev(int x) { int r = 0; while (x > 0) { r = r * 10 + x % 10; x /= 10; } return r; }
    public static int lc_count_nice_pairs_csv(String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) { int v = Integer.parseInt(p[i]); a[i] = v - rev(v); } int ans = 0; for (int i = 0; i < a.length; i++) for (int j = i + 1; j < a.length; j++) if (a[i] == a[j]) ans++; return ans;
    }
}
```
