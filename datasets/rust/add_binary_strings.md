# add_binary_strings

## Problem

Return the binary sum of nonempty binary strings `a` and `b`.

## Requirements

- Inputs contain only `0` and `1`.
- Inputs are nonempty.
- Do digit-by-digit binary addition; do not require conversion to machine integer width.
- Return no leading zeros except the single string `0`.

## Source

- Source: LeetCode problem `add-binary`.
- URL: https://leetcode.com/problems/add-binary/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn add_binary_strings(a: &str, b: &str) -> String {
    let ab = a.as_bytes(); let bb = b.as_bytes();
    let mut i = ab.len() as i32 - 1; let mut j = bb.len() as i32 - 1; let mut carry = 0; let mut out: Vec<u8> = Vec::new();
    while i >= 0 || j >= 0 || carry != 0 { let mut sum = carry; if i >= 0 { sum += (ab[i as usize] - b'0') as i32; i -= 1; } if j >= 0 { sum += (bb[j as usize] - b'0') as i32; j -= 1; } out.push(b'0' + (sum % 2) as u8); carry = sum / 2; }
    out.reverse(); String::from_utf8(out).unwrap()
}
```
