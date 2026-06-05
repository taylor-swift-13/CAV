# LC Delete And Earn CSV

## Problem

Return the maximum points from the delete-and-earn rule.

## Requirements

- `nums` is a nonempty comma-separated list of positive integers less than 1000.

## Source

- Source: LeetCode problem `delete-and-earn`.
- URL: https://leetcode.com/problems/delete-and-earn/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_delete_and_earn_csv(const char *nums) {
    int points[1000] = {0}, i = 0, maxv = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } points[v] += v; if (v > maxv) maxv = v; if (nums[i] == ',') i++; }
    int take = 0, skip = 0; for (int v = 1; v <= maxv; v++) { int ntake = skip + points[v]; int nskip = take > skip ? take : skip; take = ntake; skip = nskip; } return take > skip ? take : skip;
}
```
