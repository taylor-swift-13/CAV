# LC Basic Calculator II Eval

## Problem

Evaluate an arithmetic expression with `+`, `-`, `*`, and `/`.

## Requirements

- Expression contains nonnegative integers, operators, and spaces.
- Division truncates toward zero.

## Source

- Source: LeetCode problem `basic-calculator-ii`.
- URL: https://leetcode.com/problems/basic-calculator-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_basic_calculator2_eval(s: &str) -> i32 {
    let b = s.as_bytes(); let mut stack: Vec<i32> = Vec::new(); let mut num = 0; let mut op = b'+'; let mut i = 0usize; while i <= b.len() { let ch = if i == b.len() { 0 } else { b[i] }; if ch >= b'0' && ch <= b'9' { num = num * 10 + (ch - b'0') as i32; } if (ch != b' ' && (ch < b'0' || ch > b'9')) || ch == 0 { if op == b'+' { stack.push(num); } else if op == b'-' { stack.push(-num); } else if op == b'*' { let last = stack.pop().unwrap(); stack.push(last * num); } else { let last = stack.pop().unwrap(); stack.push(last / num); } op = ch; num = 0; } i += 1; } stack.iter().sum()
}
```
