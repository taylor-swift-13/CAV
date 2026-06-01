# LC Min Stack Final Min CSV

## Problem

Simulate stack operations and return the minimum value after all operations.

## Requirements

- Operations are semicolon-separated: `push:x` or `pop`.
- The final stack is nonempty.
- Pop operations are valid.

## Source

- Source: LeetCode problem `min-stack`.
- URL: https://leetcode.com/problems/min-stack/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_stack_final_min_csv(ops: &str) -> i32 {
    let mut st: Vec<i32> = Vec::new();
    for op in ops.split(';') { if op.starts_with("push:") { st.push(op[5..].parse::<i32>().unwrap()); } else { st.pop(); } }
    let mut min = st[0]; for &v in &st { if v < min { min = v; } }
    min
}
```
