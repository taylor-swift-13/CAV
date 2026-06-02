# LC Least Unique Integers After K Removals CSV

## Problem

Return the fewest distinct integers left after removing exactly `k` elements.

## Requirements

- `arr` is a comma-separated list of integers.

## Source

- Source: LeetCode problem `least-number-of-unique-integers-after-k-removals`.
- URL: https://leetcode.com/problems/least-number-of-unique-integers-after-k-removals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_least_unique_after_k_csv(const char *arr, int k) {
    int a[512], n = 0, i = 0; while (arr[i] != '\0') { int sign = 1, v = 0; if (arr[i] == '-') { sign = -1; i++; } while (arr[i] >= '0' && arr[i] <= '9') { v = v * 10 + arr[i] - '0'; i++; } a[n++] = sign * v; if (arr[i] == ',') i++; } int freq[512], f = 0; for (int x = 0; x < n; x++) { int seen = 0; for (int y = 0; y < x; y++) if (a[y] == a[x]) seen = 1; if (!seen) { int c = 0; for (int y = 0; y < n; y++) if (a[y] == a[x]) c++; freq[f++] = c; } } for (int x = 0; x < f; x++) for (int y = x + 1; y < f; y++) if (freq[y] < freq[x]) { int t = freq[x]; freq[x] = freq[y]; freq[y] = t; } int left = f; for (int x = 0; x < f && k >= freq[x]; x++) { k -= freq[x]; left--; } return left;
}
```
