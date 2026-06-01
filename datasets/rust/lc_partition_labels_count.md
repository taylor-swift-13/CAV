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

```rust
pub fn lc_partition_labels_count(s: &str) -> i32 {
    let b = s.as_bytes(); let mut last = [0usize; 26]; let mut i = 0usize; while i < b.len() { last[(b[i] - b'a') as usize] = i; i += 1; } let mut ans = 0; let mut end = 0usize; i = 0; while i < b.len() { let l = last[(b[i] - b'a') as usize]; if l > end { end = l; } if i == end { ans += 1; } i += 1; } ans
}
```
