# length_of_last_word

## Problem

Return the length of the last word in string `s`.

## Requirements

- `s` contains printable ASCII letters and spaces.
- There is at least one non-space character.
- A word is a maximal contiguous sequence of non-space characters.
- Trailing spaces must be ignored.
- Only the length is returned; the last word itself is not returned.

## Source

- Source: LeetCode problem `length-of-last-word`.
- URL: https://leetcode.com/problems/length-of-last-word/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn length_of_last_word(s: &str) -> i32 {
    let bytes = s.as_bytes();
    let mut i: i32 = bytes.len() as i32 - 1;
    while i >= 0 && bytes[i as usize] == b' ' { i -= 1; }
    let mut count = 0;
    while i >= 0 && bytes[i as usize] != b' ' { count += 1; i -= 1; }
    count
}
```
