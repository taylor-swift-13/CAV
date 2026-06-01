# LC Shortest Unsorted Continuous Subarray Length CSV

## Problem

Return the shortest subarray length that must be sorted to make the whole array sorted.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `shortest-unsorted-continuous-subarray`.
- URL: https://leetcode.com/problems/shortest-unsorted-continuous-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_shortest_unsorted_len_csv(const char *nums) {
    int a[512], b[512], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n] = b[n] = sign * v; n++; if (nums[i] == ',') i++; } for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (b[y] < b[x]) { int t = b[x]; b[x] = b[y]; b[y] = t; } int l = 0; while (l < n && a[l] == b[l]) l++; if (l == n) return 0; int r = n - 1; while (r >= 0 && a[r] == b[r]) r--; return r - l + 1;
}
```
