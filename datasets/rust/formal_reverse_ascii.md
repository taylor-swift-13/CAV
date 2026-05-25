# formal_reverse_ascii

## Problem

Return the reverse of ASCII string `s`.

## Requirements

- Input is an ASCII string.
- The empty string reverses to the empty string.
- Return a new reversed string.
- Do not drop punctuation or spaces.

## Source

- Source: FormalBench-inspired program `string-reverse`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn formal_reverse_ascii(s: &str) -> String {
    s.chars().rev().collect()
}
```
