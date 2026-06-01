# LC String To Integer Atoi Value

## Problem

Parse a string as a 32-bit signed integer following atoi rules.

## Requirements

- Skip leading spaces, parse optional sign and digits, then clamp to 32-bit signed range.

## Source

- Source: LeetCode problem `string-to-integer-atoi`.
- URL: https://leetcode.com/problems/string-to-integer-atoi/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_atoi_value(s: &str) -> i32 {
    let b = s.as_bytes(); let mut i = 0usize; while i < b.len() && b[i] == b' ' { i += 1; } let mut sign = 1i64; if i < b.len() && (b[i] == b'+' || b[i] == b'-') { if b[i] == b'-' { sign = -1; } i += 1; } let mut val = 0i64; while i < b.len() && b[i] >= b'0' && b[i] <= b'9' { val = val * 10 + (b[i] - b'0') as i64; if sign == 1 && val > i32::MAX as i64 { return i32::MAX; } if sign == -1 && val > 2147483648 { return i32::MIN; } i += 1; } (sign * val) as i32
}
```
