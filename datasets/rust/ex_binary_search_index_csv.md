# Exercism Binary Search Index CSV

## Problem

Return the index of `target` in a sorted comma-separated array, or `-1` if absent.

## Requirements

- The empty string represents an empty array.
- Values are sorted ascending.

## Source

- Source: Exercism problem `binary-search`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/binary-search
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_binary_search_index_csv(nums: &str, target: i32) -> i32 {
    if nums.is_empty() { return -1; }
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    let mut l = 0i32; let mut r = a.len() as i32 - 1;
    while l <= r { let m = l + (r - l) / 2; let v = a[m as usize]; if v == target { return m; } if v < target { l = m + 1; } else { r = m - 1; } }
    -1
}
```
