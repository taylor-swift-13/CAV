# LC Number Of LIS Count CSV

## Problem

Return how many longest increasing subsequences exist.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `number-of-longest-increasing-subsequence`.
- URL: https://leetcode.com/problems/number-of-longest-increasing-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_number_of_lis_count_csv(const char *nums) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = sign * v; n++; if (nums[i] == ',') i++; } int len[256], cnt[256], best = 0, ans = 0; for (int x = 0; x < n; x++) { len[x] = 1; cnt[x] = 1; for (int y = 0; y < x; y++) if (a[y] < a[x]) { if (len[y] + 1 > len[x]) { len[x] = len[y] + 1; cnt[x] = cnt[y]; } else if (len[y] + 1 == len[x]) cnt[x] += cnt[y]; } if (len[x] > best) { best = len[x]; ans = cnt[x]; } else if (len[x] == best) ans += cnt[x]; } return ans;
}
```
