# middle_node_value_csv

## Problem

Treat comma-separated integer string `list` as a linked list and return the value of its middle node.

## Requirements

- `list` is nonempty and comma-separated with no spaces.
- For an even number of nodes, return the second middle value.
- Return the node value, not the index.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `middle-of-the-linked-list`.
- URL: https://leetcode.com/problems/middle-of-the-linked-list/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn middle_node_value_csv(list: &str) -> i32 {
    let p: Vec<i32> = list.split(',').map(|x| x.parse::<i32>().unwrap()).collect();
    p[p.len() / 2]
}
```
