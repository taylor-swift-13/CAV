# LC Compare Version Result

## Problem

Compare two version strings and return `-1`, `0`, or `1`.

## Requirements

- Version revisions are dot-separated nonnegative integers.
- Leading zeroes are ignored.

## Source

- Source: LeetCode problem `compare-version-numbers`.
- URL: https://leetcode.com/problems/compare-version-numbers/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_compare_version_result(version1: &str, version2: &str) -> i32 {
    let a: Vec<i64> = version1.split('.').map(|x| x.parse::<i64>().unwrap()).collect(); let b: Vec<i64> = version2.split('.').map(|x| x.parse::<i64>().unwrap()).collect(); let n = if a.len() > b.len() { a.len() } else { b.len() }; let mut i = 0usize; while i < n { let x = if i < a.len() { a[i] } else { 0 }; let y = if i < b.len() { b[i] } else { 0 }; if x < y { return -1; } if x > y { return 1; } i += 1; } 0
}
```
