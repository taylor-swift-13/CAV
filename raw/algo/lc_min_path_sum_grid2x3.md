# LC Min Path Sum 2x3

## Problem

Return the minimum path sum from top-left to bottom-right in a 2x3 grid moving only right or down.

## Requirements

- Grid values are supplied row-major.
- All values are nonnegative.

## Source

- Source: LeetCode problem `minimum-path-sum`.
- URL: https://leetcode.com/problems/minimum-path-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_min_path_sum_grid2x3(int a00, int a01, int a02, int a10, int a11, int a12) {
    int d00 = a00;
    int d01 = d00 + a01;
    int d02 = d01 + a02;
    int d10 = d00 + a10;
    int d11 = (d01 < d10 ? d01 : d10) + a11;
    int d12 = (d02 < d11 ? d02 : d11) + a12;
    return d12;
}
```
