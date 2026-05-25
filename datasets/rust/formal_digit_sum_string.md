# formal_digit_sum_string

## Problem

Return the sum of decimal digit characters in ASCII string `s`.

## Requirements

- Input is ASCII.
- Only digit characters contribute.
- Non-digits are ignored.
- Return the arithmetic sum of digit values.

## Source

- Source: FormalBench-inspired program `string-digit-sum`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn formal_digit_sum_string(s: &str) -> i32 {
    s.bytes().filter(|&b| b >= b'0' && b <= b'9').map(|b| (b - b'0') as i32).sum()
}
```
