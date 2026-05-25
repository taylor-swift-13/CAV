# decode_xored_array_csv

## Problem

Given comma-separated XOR-encoded values and the first original value, return the decoded array.

## Requirements

- `encoded[i] = arr[i] XOR arr[i+1]`.
- `encoded` is comma-separated nonnegative integers.
- The empty string means the original array only contains `first`.
- Return the decoded array as comma-separated integers.

## Source

- Source: LeetCode problem `decode-xored-array`.
- URL: https://leetcode.com/problems/decode-xored-array/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn decode_xored_array_csv(encoded: &str, first: i32) -> String {
    let mut cur = first; let mut out = vec![cur.to_string()];
    if !encoded.is_empty() { for p in encoded.split(',') { cur ^= p.parse::<i32>().unwrap(); out.push(cur.to_string()); } }
    out.join(",")
}
```
