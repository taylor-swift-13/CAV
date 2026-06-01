# LC Binary Subarrays With Sum Count CSV

## Problem

Return how many nonempty contiguous subarrays have sum exactly `goal`.

## Requirements

- `nums` is a comma-separated binary array.

## Source

- Source: LeetCode problem `binary-subarrays-with-sum`.
- URL: https://leetcode.com/problems/binary-subarrays-with-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcBinarySubarraysSumCountCsv {
    public static int lc_binary_subarrays_sum_count_csv(String nums, int goal) {
        String[] p = nums.split(","); int ans = 0; for (int l = 0; l < p.length; l++) { int sum = 0; for (int r = l; r < p.length; r++) { sum += Integer.parseInt(p[r]); if (sum == goal) ans++; } } return ans;
    }
}
```
