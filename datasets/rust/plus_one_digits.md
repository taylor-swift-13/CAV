# plus_one_digits

## Problem

Return the decimal digit string representing one more than nonnegative integer string `digits`.

## Requirements

- `digits` is a nonempty string of decimal digits.
- No leading zeros appear unless the whole value is exactly `0`.
- Return the full decimal representation after adding one.
- Carry propagation must work across one or more trailing `9` digits.

## Source

- Source: LeetCode problem `plus-one`.
- URL: https://leetcode.com/problems/plus-one/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn plus_one_digits(digits: &str) -> String {
    let mut out = digits.as_bytes().to_vec();
    let mut carry = 1;
    let mut i = out.len();
    while i > 0 && carry != 0 {
        i -= 1;
        let v = (out[i] - b'0') as i32 + carry;
        out[i] = b'0' + (v % 10) as u8;
        carry = v / 10;
    }
    let mut s = String::from_utf8(out).unwrap();
    if carry != 0 { s.insert(0, '1'); }
    s
}
```
