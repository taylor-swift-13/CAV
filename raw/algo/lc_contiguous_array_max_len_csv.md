# LC Contiguous Array Max Length CSV

## Problem

Return the maximum length of a contiguous subarray with equal numbers of 0 and 1.

## Requirements

- `nums` is a comma-separated binary array.

## Source

- Source: LeetCode problem `contiguous-array`.
- URL: https://leetcode.com/problems/contiguous-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_contiguous_array_max_len_csv(const char *nums) {
    int first[1025]; for (int i = 0; i < 1025; i++) first[i] = -2; int offset = 512, sum = 0, idx = 0, best = 0, i = 0; first[offset] = -1; while (nums[i] != '\0') { sum += nums[i] == '1' ? 1 : -1; int key = sum + offset; if (first[key] == -2) first[key] = idx; else { int len = idx - first[key]; if (len > best) best = len; } idx++; i++; if (nums[i] == ',') i++; } return best;
}
```
