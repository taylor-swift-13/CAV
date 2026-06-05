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

```java
class LcNumberOfLisCountCsv {
    public static int lc_number_of_lis_count_csv(String nums) {
        String[] p = nums.split(","); int n = p.length; int[] a = new int[n], len = new int[n], cnt = new int[n]; for (int i = 0; i < n; i++) a[i] = Integer.parseInt(p[i]); int best = 0, ans = 0; for (int i = 0; i < n; i++) { len[i] = 1; cnt[i] = 1; for (int j = 0; j < i; j++) if (a[j] < a[i]) { if (len[j] + 1 > len[i]) { len[i] = len[j] + 1; cnt[i] = cnt[j]; } else if (len[j] + 1 == len[i]) cnt[i] += cnt[j]; } if (len[i] > best) { best = len[i]; ans = cnt[i]; } else if (len[i] == best) ans += cnt[i]; } return ans;
    }
}
```
