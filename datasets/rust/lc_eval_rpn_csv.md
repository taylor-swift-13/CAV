# LC Evaluate RPN CSV

## Problem

Evaluate a reverse Polish notation expression encoded as comma-separated tokens.

## Requirements

- Tokens are integers or one of `+`, `-`, `*`, `/`.
- Division truncates toward zero.
- The expression is valid.

## Source

- Source: LeetCode problem `evaluate-reverse-polish-notation`.
- URL: https://leetcode.com/problems/evaluate-reverse-polish-notation/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_eval_rpn_csv(tokens: &str) -> i32 {
    let mut stack: Vec<i32> = Vec::new();
    for raw in tokens.split(',') { let t = raw.trim(); match t { "+" => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(a + b); }, "-" => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(a - b); }, "*" => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(a * b); }, "/" => { let b = stack.pop().unwrap(); let a = stack.pop().unwrap(); stack.push(a / b); }, _ => stack.push(t.parse::<i32>().unwrap()), } }
    stack[0]
}
```
