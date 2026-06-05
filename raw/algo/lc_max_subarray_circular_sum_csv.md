# LC Maximum Circular Subarray Sum CSV

## Problem

Return the maximum nonempty subarray sum in a circular array.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `maximum-sum-circular-subarray`.
- URL: https://leetcode.com/problems/maximum-sum-circular-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_max_subarray_circular_sum_csv(const char *nums) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = sign * v; n++; if (nums[i] == ',') i++; }
    int total = a[0], maxcur = a[0], maxsum = a[0], mincur = a[0], minsum = a[0]; for (int j = 1; j < n; j++) { int x = a[j]; total += x; maxcur = x > maxcur + x ? x : maxcur + x; if (maxcur > maxsum) maxsum = maxcur; mincur = x < mincur + x ? x : mincur + x; if (mincur < minsum) minsum = mincur; } if (maxsum < 0) return maxsum; return maxsum > total - minsum ? maxsum : total - minsum;
}
```
