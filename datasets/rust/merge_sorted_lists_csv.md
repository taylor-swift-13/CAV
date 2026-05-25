# merge_sorted_lists_csv

## Problem

Treat `a` and `b` as sorted linked lists encoded by comma-separated integers and return their sorted merge.

## Requirements

- Each input is a sorted comma-separated integer list with no spaces.
- The empty string represents an empty list.
- Return all values in nondecreasing order.
- At most 64 integers are encoded per input.

## Source

- Source: LeetCode problem `merge-two-sorted-lists`.
- URL: https://leetcode.com/problems/merge-two-sorted-lists/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn merge_sorted_lists_csv(a: &str, b: &str) -> String {
    let av: Vec<i32> = if a.is_empty() { Vec::new() } else { a.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };
    let bv: Vec<i32> = if b.is_empty() { Vec::new() } else { b.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };
    let mut i = 0usize;
    let mut j = 0usize;
    let mut out: Vec<String> = Vec::new();
    while i < av.len() || j < bv.len() { let v; if j >= bv.len() || (i < av.len() && av[i] <= bv[j]) { v = av[i]; i += 1; } else { v = bv[j]; j += 1; } out.push(v.to_string()); }
    out.join(",")
}
```
