# reverse_list_csv

## Problem

Treat comma-separated integer string `list` as a linked list and return its values in reverse order.

## Requirements

- `list` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty list.
- Return a comma-separated string using the same integer spelling after parsing.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `reverse-linked-list`.
- URL: https://leetcode.com/problems/reverse-linked-list/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn reverse_list_csv(list: &str) -> String {
    if list.is_empty() { return String::new(); }
    let mut p: Vec<&str> = list.split(',').collect();
    p.reverse();
    p.join(",")
}
```
