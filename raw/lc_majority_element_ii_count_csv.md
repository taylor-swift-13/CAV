# LC Majority Element II Count CSV

## Problem

Return how many distinct values appear more than `n/3` times.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.
- The answer is at most 2.

## Source

- Source: LeetCode problem `majority-element-ii`.
- URL: https://leetcode.com/problems/majority-element-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_majority_element_ii_count_csv(const char *nums) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }
    int ans = 0; for (int x = 0; x < n; x++) { int seen = 0; for (int y = 0; y < x; y++) if (a[y] == a[x]) seen = 1; if (!seen) { int cnt = 0; for (int y = 0; y < n; y++) if (a[y] == a[x]) cnt++; if (cnt > n / 3) ans++; } } return ans;
}
```
