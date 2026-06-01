# LC Degree Of Array Shortest Subarray CSV

## Problem

Return the shortest contiguous subarray length with the same degree as the whole array.

## Requirements

- `nums` is a nonempty comma-separated list of nonnegative integers less than 1000.

## Source

- Source: LeetCode problem `degree-of-an-array`.
- URL: https://leetcode.com/problems/degree-of-an-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_degree_shortest_subarray_csv(const char *nums) {
    int first[1000], count[1000] = {0}, best = 1000000, degree = 0, idx = 0, i = 0; for (int k = 0; k < 1000; k++) first[k] = -1;
    while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } if (first[v] < 0) first[v] = idx; count[v]++; int len = idx - first[v] + 1; if (count[v] > degree) { degree = count[v]; best = len; } else if (count[v] == degree && len < best) best = len; idx++; if (nums[i] == ',') i++; }
    return best;
}
```
