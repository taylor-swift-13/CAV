# LC Maximum Length Of Repeated Subarray

## Problem

Return the maximum length of a subarray appearing in both arrays.

## Requirements

- Arrays are comma-separated integer lists.

## Source

- Source: LeetCode problem `maximum-length-of-repeated-subarray`.
- URL: https://leetcode.com/problems/maximum-length-of-repeated-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_repeated_subarray_max_len(const char *nums1, const char *nums2) {
    int a[256], b[256], n = 0, m = 0, i = 0; while (nums1[i] != '\0') { int v = 0; while (nums1[i] >= '0' && nums1[i] <= '9') { v = v * 10 + (nums1[i] - '0'); i++; } a[n++] = v; if (nums1[i] == ',') i++; } i = 0; while (nums2[i] != '\0') { int v = 0; while (nums2[i] >= '0' && nums2[i] <= '9') { v = v * 10 + (nums2[i] - '0'); i++; } b[m++] = v; if (nums2[i] == ',') i++; } int dp[257][257] = {{0}}, best = 0; for (int x = 1; x <= n; x++) for (int y = 1; y <= m; y++) if (a[x - 1] == b[y - 1]) { dp[x][y] = dp[x - 1][y - 1] + 1; if (dp[x][y] > best) best = dp[x][y]; } return best;
}
```
