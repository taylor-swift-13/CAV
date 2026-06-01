# LC Max Consecutive Ones III Length CSV

## Problem

Return the longest subarray of ones after flipping at most `k` zeroes.

## Requirements

- `nums` is a comma-separated list containing only `0` and `1`.

## Source

- Source: LeetCode problem `max-consecutive-ones-iii`.
- URL: https://leetcode.com/problems/max-consecutive-ones-iii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLongestOnesKFlipsCsv {
    public static int lc_longest_ones_k_flips_csv(String nums, int k) {
        String[] p = nums.split(","); int left = 0, zeros = 0, best = 0; for (int right = 0; right < p.length; right++) { if (p[right].equals("0")) zeros++; while (zeros > k) { if (p[left].equals("0")) zeros--; left++; } best = Math.max(best, right - left + 1); } return best;
    }
}
```
