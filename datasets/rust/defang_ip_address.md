# defang_ip_address

## Problem

Return the defanged form of an IPv4 address by replacing each `.` with `[.]`.

## Requirements

- Input is an IPv4 address string.
- Replace every period with the three-character sequence `[.]`.
- All other characters are copied unchanged.
- Return the transformed string.

## Source

- Source: LeetCode problem `defanging-an-ip-address`.
- URL: https://leetcode.com/problems/defanging-an-ip-address/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn defang_ip_address(address: &str) -> String {
    let mut out = String::new();
    for c in address.chars() { if c == '.' { out.push_str("[.]"); } else { out.push(c); } }
    out
}
```
