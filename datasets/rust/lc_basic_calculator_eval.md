# LC Basic Calculator Eval

## Problem

Evaluate an arithmetic expression with `+`, `-`, parentheses, and spaces.

## Requirements

- Expression contains nonnegative integers, plus/minus signs, parentheses, and spaces.

## Source

- Source: LeetCode problem `basic-calculator`.
- URL: https://leetcode.com/problems/basic-calculator/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_basic_calculator_eval(s: &str) -> i32 {
    let mut stack: Vec<i32> = Vec::new(); let mut res = 0; let mut num = 0; let mut sign = 1; for ch in s.bytes() { if ch >= b'0' && ch <= b'9' { num = num * 10 + (ch - b'0') as i32; } else if ch == b'+' { res += sign * num; num = 0; sign = 1; } else if ch == b'-' { res += sign * num; num = 0; sign = -1; } else if ch == b'(' { stack.push(res); stack.push(sign); res = 0; sign = 1; } else if ch == b')' { res += sign * num; num = 0; let prev_sign = stack.pop().unwrap(); let prev_res = stack.pop().unwrap(); res = prev_res + prev_sign * res; } } res + sign * num
}
```
