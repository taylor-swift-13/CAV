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

```c
int lc_longest_ones_k_flips_csv(const char *nums, int k) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { a[n] = nums[i] - '0'; n++; i++; if (nums[i] == ',') i++; } int left = 0, zeros = 0, best = 0; for (int right = 0; right < n; right++) { if (a[right] == 0) zeros++; while (zeros > k) { if (a[left] == 0) zeros--; left++; } int len = right - left + 1; if (len > best) best = len; } return best;
}
```
