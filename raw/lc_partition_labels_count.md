# LC Partition Labels Count

## Problem

Return the number of partitions made by the partition-labels greedy algorithm.

## Requirements

- Input contains lowercase English letters.
- Each letter appears in at most one returned partition.

## Source

- Source: LeetCode problem `partition-labels`.
- URL: https://leetcode.com/problems/partition-labels/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_partition_labels_count(const char *s) {
    int last[26] = {0}; for (int i = 0; s[i] != '\0'; i++) last[s[i] - 'a'] = i; int ans = 0, end = 0; for (int i = 0; s[i] != '\0'; i++) { if (last[s[i] - 'a'] > end) end = last[s[i] - 'a']; if (i == end) ans++; } return ans;
}
```
