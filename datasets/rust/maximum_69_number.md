# maximum_69_number

## Problem

Given a positive decimal integer containing only digits `6` and `9`, change at most one `6` to `9` to maximize it.

## Requirements

- `num` contains only decimal digits `6` and `9`.
- Change at most one digit.
- Changing the leftmost `6` gives the maximum result.
- If there is no `6`, return `num` unchanged.

## Source

- Source: LeetCode problem `maximum-69-number`.
- URL: https://leetcode.com/problems/maximum-69-number/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn maximum_69_number(num: i32) -> i32 {
    let mut place = 1; let mut best = 0; let mut temp = num;
    while temp > 0 { let d = temp % 10; if d == 6 { best = place; } place *= 10; temp /= 10; }
    num + best * 3
}
```
